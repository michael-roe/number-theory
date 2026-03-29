import Mathlib

--
-- Outline of proof
--
-- m is odd
-- n is even
-- gcd(m, n) = 1
-- Let d = gcd(m + n, m - n)
-- d divides (m + n) + (m - n) = 2*m
-- d divides (m + n) - (m - n) = 2*n
-- gcd(2*m, 2*n) = 2*gcd(m, n) = 2
-- So d is 1 or 2
-- But m + n and m - n are both odd
-- Therefore d is 1

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

  have h_gcd_2m_2n : Int.gcd (2 * m) (2 * n) = 2 * Int.gcd m n := by
    rw [Int.gcd_mul_left]
    simp

  have h_d_dvd_gcd : (d : ℤ) ∣ ((2 * m).gcd (2 * n) : ℤ) :=
    Int.dvd_coe_gcd h_d_dvd_2m h_d_dvd_2n

  rw [h_gcd_2m_2n, h_coprime] at h_d_dvd_gcd
  simp only [Nat.cast_ofNat, mul_one] at h_d_dvd_gcd

  have h_d_dvd_gcd_cast : (d : ℕ) ∣ 2 :=
    Int.natCast_dvd_natCast.mp h_d_dvd_gcd

  have h_factors_of_two: (d : ℕ) ∣ 2 ↔  d = 1 ∨ d = 2 :=
    Nat.dvd_prime Nat.prime_two

  have h_one_or_two : d = 1 ∨ d = 2 := h_factors_of_two.mp h_d_dvd_gcd_cast

  have h_one : d = 1 := by
    cases h_one_or_two with
    | inl h => exact h
    | inr h =>
      rw [h] at hd_dvd_sum
      have h_2_dvd : (2 : ℤ) ∣ (m + n) := hd_dvd_sum
      have : (m + n) % 2 = 0 := Int.emod_eq_zero_of_dvd h_2_dvd
      rw [this] at h_sum_odd
      norm_num at h_sum_odd

  exact h_one
