import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12318

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    (List.ofFn x).getD u false = x ⟨u, hu⟩ := by
  simp [List.getD_eq_getElem?_getD, hu]

theorem tpoly_le (p : Polynomial ℕ) (n : ℕ) (hn : 1 ≤ n) :
    p.eval n ≤ (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i) * n ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hn hi')

theorem tp4 (l : ℕ) (hl : 16 ≤ l) : l ^ 4 ≤ 2 ^ l := by
  induction l, hl using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h2 : 16 * n ≤ n ^ 2 := by nlinarith
    have h3 : 16 * n ^ 2 ≤ n ^ 3 := by nlinarith
    have h4 : 16 * n ^ 3 ≤ n ^ 4 := by nlinarith
    have : (n + 1) ^ 4 ≤ 2 * n ^ 4 := by
      have e : (n + 1) ^ 4 = n ^ 4 + 4 * n ^ 3 + 6 * n ^ 2 + 4 * n + 1 := by ring
      rw [e]; omega
    calc (n + 1) ^ 4 ≤ 2 * n ^ 4 := this
      _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left _ ih
      _ = 2 ^ (n + 1) := by ring

theorem tpbound (p : Polynomial ℕ) (K : ℕ) : ∃ k, K ≤ k ∧ 2 * p.eval (2 * k) ≤ 2 ^ k := by
  obtain ⟨Cs, hCs⟩ : ∃ c, c = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = p.natDegree := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = 4 * (Cs + 1) * (d + 1) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = max K B + 16 := ⟨_, rfl⟩
  have hqK : K ≤ q := by omega
  have hqB : B ≤ q := by omega
  have hq16 : 16 ≤ q := by omega
  have hdq : q ≤ (d + 1) * q := Nat.le_mul_of_pos_left _ (by omega)
  refine ⟨(d + 1) * q, by omega, ?_⟩
  have hk1 : 1 ≤ 2 * ((d + 1) * q) := by omega
  have h1 := tpoly_le p (2 * ((d + 1) * q)) hk1
  rw [← hCs, ← hd] at h1
  have h2 : (2 * ((d + 1) * q)) ^ d ≤ (2 * ((d + 1) * q)) ^ (d + 1) :=
    Nat.pow_le_pow_right hk1 (by omega)
  have h3 : 2 * Cs ≤ (2 * (Cs + 1)) ^ (d + 1) :=
    le_trans (by omega) (Nat.le_self_pow (by omega) _)
  have h4 : 2 * (Cs + 1) * (2 * ((d + 1) * q)) = B * q := by rw [hB]; ring
  have h5 : B * q ≤ 2 ^ q := by
    calc B * q ≤ q * q := Nat.mul_le_mul_right _ hqB
      _ = q ^ 2 := (sq q).symm
      _ ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
      _ ≤ 2 ^ q := tp4 q hq16
  calc 2 * p.eval (2 * ((d + 1) * q)) ≤ 2 * (Cs * (2 * ((d + 1) * q)) ^ d) :=
        Nat.mul_le_mul_left _ h1
    _ ≤ 2 * Cs * (2 * ((d + 1) * q)) ^ (d + 1) := by
        rw [← Nat.mul_assoc 2 Cs]; exact Nat.mul_le_mul_left _ h2
    _ ≤ (2 * (Cs + 1)) ^ (d + 1) * (2 * ((d + 1) * q)) ^ (d + 1) := Nat.mul_le_mul_right _ h3
    _ = (B * q) ^ (d + 1) := by rw [← mul_pow, h4]
    _ ≤ (2 ^ q) ^ (d + 1) := Nat.pow_le_pow_left h5 _
    _ = 2 ^ ((d + 1) * q) := by rw [← pow_mul, mul_comm]

theorem tadj_cast (A : (k : ℕ) → Fin (2 ^ k) → Fin (2 ^ k) → Bool) (y : List Bool) (m k : ℕ)
    (h : m = k) :
    PEqualNP.Represents.adjFun (k := m) (l := m) (A m) (fun i => y.getD i false) =
      PEqualNP.Represents.adjFun (k := k) (l := k) (A k) (fun i => y.getD i false) := by
  subst h; rfl

theorem tpbound2 (p : Polynomial ℕ) (d K : ℕ) :
    ∃ m, K ≤ m ∧ 8 * d * p.eval (2 * (2 * m)) + 64 * d * m ≤ 2 ^ m := by
  obtain ⟨m, hKm, hm⟩ := tpbound
    (Polynomial.C (4 * d) * p.comp (Polynomial.C 2 * Polynomial.X) +
      Polynomial.C (16 * d) * Polynomial.X) K
  refine ⟨m, hKm, ?_⟩
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_comp] at hm
  have e : 2 * (4 * d * p.eval (2 * (2 * m)) + 16 * d * (2 * m)) =
      8 * d * p.eval (2 * (2 * m)) + 64 * d * m := by ring
  rw [e] at hm
  exact hm

theorem tarith (m d s : ℕ) (hd : 0 < d) (hpm : 8 * d * s + 64 * d * m ≤ 2 ^ m) :
    2 * s + 2 * 2 ^ (2 * m) + 2 * m * 2 ^ ((2 * m + 1) / 2) + 2 * 2 ^ (2 * m) +
      2 * m * 2 ^ ((2 * m + 1) / 2) ≤ 4 * 2 ^ (2 * m) + 2 ^ (2 * m) / d := by
  have hh : (2 * m + 1) / 2 = m := by omega
  have hp2 : 2 ^ (2 * m) = 2 ^ m * 2 ^ m := by rw [two_mul, pow_add]
  rw [hh, hp2]
  obtain ⟨a, ha⟩ : ∃ a, a = 2 ^ m := ⟨_, rfl⟩
  rw [← ha]
  rw [← ha] at hpm
  have ha1 : 1 ≤ a := by rw [ha]; exact Nat.one_le_two_pow
  have h1 : (8 * d * s + 64 * d * m) * a ≤ a * a := Nat.mul_le_mul_right a hpm
  have h2 : d * s ≤ d * s * a := Nat.le_mul_of_pos_right _ ha1
  have hq : 2 * s + 2 * m * a + 2 * m * a ≤ a * a / d := by
    rw [Nat.le_div_iff_mul_le hd]
    have e1 : (2 * s + 2 * m * a + 2 * m * a) * d = 2 * (d * s) + 4 * (d * m * a) := by ring
    have e2 : (8 * d * s + 64 * d * m) * a = 8 * (d * s * a) + 64 * (d * m * a) := by ring
    rw [e1]
    rw [e2] at h1
    omega
  omega

theorem main_aux : (∀ (k l s : ℕ) (A : Fin (2 ^ k) → Fin (2 ^ l) → Bool), PEqualNP.MetaComplexity.HasCircuitSize (k + l) (PEqualNP.Represents.adjFun A) s → PEqualNP.Represents.RepSizeAtMost A (2 * s + 2 * 2 ^ k + k * 2 ^ ((k + 1) / 2) + 2 * 2 ^ l + l * 2 ^ ((l + 1) / 2))) → ∀ (A : (k : ℕ) → Fin (2 ^ k) → Fin (2 ^ k) → Bool) (d K : ℕ), 0 < d → (∀ k, K ≤ k → ¬ PEqualNP.Represents.RepSizeAtMost (A k) (4 * 2 ^ k + 2 ^ k / d)) → {x : List Bool | Even x.length ∧ PEqualNP.Represents.adjFun (k := x.length / 2) (l := x.length / 2) (A (x.length / 2)) (fun i => x.getD i false) = true} ∈ PEqualNP.Library.NP → ¬ PEqualNP.Library.NP ⊆ PEqualNP.CircuitLowerBounds.PPoly := by
  intro hconv A d K hd hA hL hsub
  obtain ⟨p, hp⟩ := hsub hL
  simp only [PEqualNP.CircuitLowerBounds.SIZE] at hp
  obtain ⟨m, hKm, hpm⟩ := tpbound2 p d K
  apply hA (2 * m) (by omega)
  obtain ⟨C, hCg, hCs, hCd⟩ := hp (2 * (2 * m))
  have hHC : HasCircuitSize (2 * m + 2 * m) (PEqualNP.Represents.adjFun (A (2 * m)))
      (p.eval (2 * (2 * m))) := by
    refine ⟨C, hCg, hCs, ?_⟩
    intro x
    have hlen : (List.ofFn x).length = 2 * (2 * m) := by rw [List.length_ofFn]; ring
    have hd := hCd (List.ofFn x) hlen
    rw [Bool.eq_iff_iff, hd]
    have hfx : (fun i : Fin (2 * m + 2 * m) => (List.ofFn x).getD i false) = x := by
      funext i; exact ofFn_getD x i i.isLt
    have key : PEqualNP.Represents.adjFun (k := (List.ofFn x).length / 2)
        (l := (List.ofFn x).length / 2) (A ((List.ofFn x).length / 2))
        (fun i => (List.ofFn x).getD i false) = PEqualNP.Represents.adjFun (A (2 * m)) x := by
      rw [tadj_cast A (List.ofFn x) ((List.ofFn x).length / 2) (2 * m) (by rw [hlen]; omega), hfx]
    constructor
    · intro h
      obtain ⟨_, h2⟩ := h
      exact key.symm.trans h2
    · intro h
      exact And.intro (by rw [hlen]; exact even_two_mul (2 * m)) (key.trans h)
  obtain ⟨D, hD1, hD2, hD3⟩ := hconv (2 * m) (2 * m) _ (A (2 * m)) hHC
  refine ⟨D, hD1, le_trans hD2 ?_, hD3⟩
  exact tarith m d _ hd hpm

end PEqualNP.Outside.L_meta_12318

theorem PEqualNP.Outside.L_meta_12318 : (∀ (k l s : ℕ) (A : Fin (2 ^ k) → Fin (2 ^ l) → Bool), PEqualNP.MetaComplexity.HasCircuitSize (k + l) (PEqualNP.Represents.adjFun A) s → PEqualNP.Represents.RepSizeAtMost A (2 * s + 2 * 2 ^ k + k * 2 ^ ((k + 1) / 2) + 2 * 2 ^ l + l * 2 ^ ((l + 1) / 2))) → ∀ (A : (k : ℕ) → Fin (2 ^ k) → Fin (2 ^ k) → Bool) (d K : ℕ), 0 < d → (∀ k, K ≤ k → ¬ PEqualNP.Represents.RepSizeAtMost (A k) (4 * 2 ^ k + 2 ^ k / d)) → {x : List Bool | Even x.length ∧ PEqualNP.Represents.adjFun (k := x.length / 2) (l := x.length / 2) (A (x.length / 2)) (fun i => x.getD i false) = true} ∈ PEqualNP.Library.NP → ¬ PEqualNP.Library.NP ⊆ PEqualNP.CircuitLowerBounds.PPoly :=
  PEqualNP.Outside.L_meta_12318.main_aux
