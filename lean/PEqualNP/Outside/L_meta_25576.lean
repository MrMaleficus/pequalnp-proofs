import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25576

theorem main_aux : let k : Nat := 17
let rot := fun (s word : Nat) =>
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
let step := fun (word : Nat) =>
  (List.range k).foldl (fun acc b =>
    acc ||| ((xor (word.testBit b)
      (!(word.testBit ((b + 1) % k)) && word.testBit ((b + 2) % k))).toNat <<< b)) 0
let output := fun (w : Nat) =>
  ((List.range 4).foldl (fun x t =>
    step (x ^^^ rot 1 x ^^^ rot (k - 1) x) ^^^ rot (2 * t) w ^^^
      (3 ^ (k + (t + 1)) % 2 ^ k)) (rot 1 w)) >>> 8
[output 596, output (596 ^^^ 12), output 6040, output (6040 ^^^ 12),
  output 565, output (565 ^^^ 12)] = [18, 0, 0, 45, 45, 18] ∧
  ∀ label : Nat → Bool, ∃ w : BitVec 17,
    (w = 596 ∨ w = 6040 ∨ w = 565) ∧
    label (output w.toNat) = label (output (w ^^^ 12).toNat) := by
  intro k rot step output
  have hl : [output 596, output (596 ^^^ 12), output 6040, output (6040 ^^^ 12),
      output 565, output (565 ^^^ 12)] = [18, 0, 0, 45, 45, 18] := by decide +kernel
  refine ⟨hl, fun label => ?_⟩
  simp only [List.cons.injEq, and_true] at hl
  obtain ⟨a1, a2, b1, b2, c1, c2⟩ := hl
  have t1 : (596 : BitVec 17).toNat = 596 := by decide
  have t2 : ((596 : BitVec 17) ^^^ 12).toNat = 596 ^^^ 12 := by decide
  have t3 : (6040 : BitVec 17).toNat = 6040 := by decide
  have t4 : ((6040 : BitVec 17) ^^^ 12).toNat = 6040 ^^^ 12 := by decide
  have t5 : (565 : BitVec 17).toNat = 565 := by decide
  have t6 : ((565 : BitVec 17) ^^^ 12).toNat = 565 ^^^ 12 := by decide
  by_cases e1 : label 18 = label 0
  · exact ⟨596, Or.inl rfl, by rw [t1, t2, a1, a2]; exact e1⟩
  by_cases e2 : label 0 = label 45
  · exact ⟨6040, Or.inr (Or.inl rfl), by rw [t3, t4, b1, b2]; exact e2⟩
  refine ⟨565, Or.inr (Or.inr rfl), ?_⟩
  rw [t5, t6, c1, c2]
  revert e1 e2
  cases label 18 <;> cases label 0 <;> cases label 45 <;> simp

end PEqualNP.Outside.L_meta_25576

theorem PEqualNP.Outside.L_meta_25576 : let k : Nat := 17
let rot := fun (s word : Nat) =>
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
let step := fun (word : Nat) =>
  (List.range k).foldl (fun acc b =>
    acc ||| ((xor (word.testBit b)
      (!(word.testBit ((b + 1) % k)) && word.testBit ((b + 2) % k))).toNat <<< b)) 0
let output := fun (w : Nat) =>
  ((List.range 4).foldl (fun x t =>
    step (x ^^^ rot 1 x ^^^ rot (k - 1) x) ^^^ rot (2 * t) w ^^^
      (3 ^ (k + (t + 1)) % 2 ^ k)) (rot 1 w)) >>> 8
[output 596, output (596 ^^^ 12), output 6040, output (6040 ^^^ 12),
  output 565, output (565 ^^^ 12)] = [18, 0, 0, 45, 45, 18] ∧
  ∀ label : Nat → Bool, ∃ w : BitVec 17,
    (w = 596 ∨ w = 6040 ∨ w = 565) ∧
    label (output w.toNat) = label (output (w ^^^ 12).toNat) :=
  PEqualNP.Outside.L_meta_25576.main_aux
