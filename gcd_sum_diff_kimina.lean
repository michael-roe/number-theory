import Mathlib

-- This version created by Kimina Prover

theorem gcd_sum_diff (m n : ℤ)
  (h_m_odd : m % 2 = 1)
  (h_n_even : n % 2 = 0)
  (h_coprime : m.gcd n = 1) :
  (m + n).gcd (m - n) = 1 := by
  have h_sum_odd : (m + n) % 2 = 1 := by
    rw [Int.add_emod, h_m_odd, h_n_even]
    norm_num
  have h_diff_odd : (m - n) % 2 = 1 := by
    rw [Int.sub_emod, h_m_odd, h_n_even]
    norm_num
  let d := (m + n).gcd (m - n)
  have hd_dvd_sum : (d : ℤ) ∣ (m + n) := Int.gcd_dvd_left _ _
  have hd_dvd_diff : (d : ℤ) ∣ (m - n) := Int.gcd_dvd_right _ _
  -- d divides (m + n) + (m - n) = 2*m
  have h_d_dvd_2m : (d : ℤ) ∣ 2 * m := by
    have h1 : (d : ℤ) ∣ (m + n) + (m - n) := dvd_add hd_dvd_sum hd_dvd_diff
    convert h1 using 1
    ring
  -- d divides (m + n) - (m - n) = 2*n
  have h_d_dvd_2n : (d : ℤ) ∣ 2 * n := by
    have h1 : (d : ℤ) ∣ (m + n) - (m - n) := dvd_sub hd_dvd_sum hd_dvd_diff
    convert h1 using 1
    ring
  -- Since d divides both 2*m and 2*n, and gcd(m, n) = 1, we have d | 2
  have h_d_dvd_2 : (d : ℤ) ∣ 2 := by
    have h_gcd_2m_2n : (2 * m).gcd (2 * n) = 2 * m.gcd n := Int.gcd_mul_left 2 m n
    rw [h_coprime] at h_gcd_2m_2n
    simp only [mul_one] at h_gcd_2m_2n
    have h_d_dvd_gcd : (d : ℤ) ∣ ((2 * m).gcd (2 * n) : ℤ) := Int.dvd_coe_gcd h_d_dvd_2m h_d_dvd_2n
    rw [h_gcd_2m_2n] at h_d_dvd_gcd
    exact h_d_dvd_gcd
  -- But m + n is odd, so 2 does not divide m + n
  have h_2_not_dvd_sum : ¬((2 : ℤ) ∣ (m + n)) := by
    intro h_contra
    obtain ⟨c, hc⟩ := h_contra
    have : (m + n) % 2 = 0 := by
      rw [hc, Int.mul_emod_right]
    rw [this] at h_sum_odd
    norm_num at h_sum_odd
  -- Therefore 2 does not divide d
  have h_2_not_dvd_d : ¬((2 : ℤ) ∣ (d : ℤ)) := by
    intro h_contra
    have : (2 : ℤ) ∣ (m + n) := dvd_trans h_contra hd_dvd_sum
    exact h_2_not_dvd_sum this
  -- So d must be 1
  have h_d_eq_1 : d = 1 := by
    obtain ⟨k, hk⟩ := h_d_dvd_2
    have h_d_pos : 0 < d := by
      by_contra h_not_pos
      push_neg at h_not_pos
      have : d = 0 := by omega
      simp [this] at hk
    have h_d_le_2 : d ≤ 2 := by
      by_contra h_not_le
      push_neg at h_not_le
      have h_3_le : 3 ≤ d := h_not_le
      have : 2 < (d : ℤ) := by omega
      have hk_pos : 0 < k := by
        by_contra h_k_not_pos
        push_neg at h_k_not_pos
        have h_k_le : k ≤ 0 := by omega
        have : (d : ℤ) * k ≤ 0 := by
          nlinarith [sq_nonneg k, sq_nonneg (d : ℤ)]
        rw [← hk] at this
        omega
      have : 3 ≤ (d : ℤ) * k := by
        calc (d : ℤ) * k ≥ 3 * k := by nlinarith [sq_nonneg k]
          _ ≥ 3 * 1 := by nlinarith [sq_nonneg k]
          _ = 3 := by ring
      rw [← hk] at this
      omega
    have : d = 1 ∨ d = 2 := by omega
    cases this with
    | inl h => exact h
    | inr h =>
      have : (2 : ℤ) ∣ (d : ℤ) := by
        rw [h]
        norm_num
      exact absurd this h_2_not_dvd_d
  change (m + n).gcd (m - n) = 1
  rw [← h_d_eq_1]
