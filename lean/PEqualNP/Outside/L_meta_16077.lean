import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_16077

theorem div_step (e m : ℕ) (he : 1 ≤ e) : m ≤ e * (m / e) + e := by
  have h := Nat.div_add_mod m e
  have hm : m % e < e := Nat.mod_lt _ (by omega)
  nlinarith

theorem grow (r : ℕ → ℕ) (K e : ℕ) (he : 1 ≤ e)
    (h : ∀ k : ℕ, K ≤ k → 2 * r k + 2 ^ k / e ≤ r (k + 1)) :
    ∀ j : ℕ, j * 2 ^ (K + j) ≤ 2 * (e * r (K + j)) + 2 * e * (2 ^ j - 1) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have hs := h (K + j) (by omega)
    have hd := div_step e (2 ^ (K + j)) he
    have hp : 2 ^ (K + j + 1) = 2 * 2 ^ (K + j) := by rw [pow_succ]; ring
    have hq : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
    have hj1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    rw [show K + (j + 1) = K + j + 1 by omega, hp, hq]
    have h1 : e * (2 * r (K + j) + 2 ^ (K + j) / e) ≤ e * r (K + j + 1) := Nat.mul_le_mul_left e hs
    have h2 : 2 * e * (2 * 2 ^ j - 1) = 2 * (2 * e * (2 ^ j - 1)) + 2 * e := by
      have : 2 * 2 ^ j - 1 = 2 * (2 ^ j - 1) + 1 := by omega
      rw [this]; ring
    rw [h2]
    nlinarith [ih, h1, hd]

theorem main_aux : ∀ (r : ℕ → ℕ) (K e : ℕ), 1 ≤ e → (∀ k : ℕ, K ≤ k → 2 * r k + 2 ^ k / e ≤ r (k + 1)) → ∀ d : ℕ, 1 ≤ d → ∃ K' : ℕ, ∀ k : ℕ, K' ≤ k → 4 * 2 ^ k + 2 ^ k / d < r k := by
  intro r K e he h d hd
  refine ⟨K + 14 * e + 1, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = K + j := ⟨k - K, by omega⟩
  have g := grow r K e he h j
  have hdiv : 2 ^ (K + j) / d ≤ 2 ^ (K + j) := Nat.div_le_self _ _
  have hp : 2 ^ (K + j) = 2 ^ K * 2 ^ j := pow_add 2 K j
  have hK : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  have hj : 14 * e + 1 ≤ j := by omega
  have hsub : 2 * e * (2 ^ j - 1) ≤ 2 * e * 2 ^ j := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have key : 6 * e * 2 ^ (K + j) < e * r (K + j) := by
    have h3 : 2 * e * 2 ^ j ≤ 2 * e * 2 ^ (K + j) := by
      rw [hp]; exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
    have h4 : (14 * e + 1) * 2 ^ (K + j) ≤ j * 2 ^ (K + j) := Nat.mul_le_mul_right _ hj
    have h5 : 0 < 2 ^ (K + j) := Nat.two_pow_pos _
    have h6 : (14 * e + 1) * 2 ^ (K + j) = 14 * (e * 2 ^ (K + j)) + 2 ^ (K + j) := by ring
    nlinarith [g, h3, hsub, h4, h5]
  have he0 : 0 < e := by omega
  by_contra hc
  push_neg at hc
  have h8 : e * r (K + j) ≤ e * (4 * 2 ^ (K + j) + 2 ^ (K + j) / d) := Nat.mul_le_mul_left e hc
  have h9 : e * (4 * 2 ^ (K + j) + 2 ^ (K + j) / d) ≤ e * (5 * 2 ^ (K + j)) := Nat.mul_le_mul_left e (by omega)
  have h10 : e * (5 * 2 ^ (K + j)) = 5 * (e * 2 ^ (K + j)) := by ring
  have h11 : 6 * e * 2 ^ (K + j) = 6 * (e * 2 ^ (K + j)) := by ring
  have h12 : 0 < e * 2 ^ (K + j) := Nat.mul_pos he0 (Nat.two_pow_pos _)
  nlinarith [key, h8, h9, h10, h11, h12]

end PEqualNP.Outside.L_meta_16077

theorem PEqualNP.Outside.L_meta_16077 : ∀ (r : ℕ → ℕ) (K e : ℕ), 1 ≤ e → (∀ k : ℕ, K ≤ k → 2 * r k + 2 ^ k / e ≤ r (k + 1)) → ∀ d : ℕ, 1 ≤ d → ∃ K' : ℕ, ∀ k : ℕ, K' ≤ k → 4 * 2 ^ k + 2 ^ k / d < r k := PEqualNP.Outside.L_meta_16077.main_aux
