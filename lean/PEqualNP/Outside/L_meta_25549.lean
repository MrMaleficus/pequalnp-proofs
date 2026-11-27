import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25549

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
output 128218 = 100 ∧ output 128222 = 100 ∧
  ∀ label : Nat → Bool, ∃ w : BitVec 17,
    label (output w.toNat) = label (output (w ^^^ 4).toNat) := by
  intro k rot step output
  have h1 : output 128218 = 100 := by decide +kernel
  have h2 : output 128222 = 100 := by decide +kernel
  refine ⟨h1, h2, fun label => ⟨BitVec.ofNat 17 128218, ?_⟩⟩
  have e1 : (BitVec.ofNat 17 128218).toNat = 128218 := by decide
  have e2 : (BitVec.ofNat 17 128218 ^^^ 4).toNat = 128222 := by decide
  rw [e1, e2, h1, h2]

end PEqualNP.Outside.L_meta_25549

theorem PEqualNP.Outside.L_meta_25549 : let k : Nat := 17
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
output 128218 = 100 ∧ output 128222 = 100 ∧
  ∀ label : Nat → Bool, ∃ w : BitVec 17,
    label (output w.toNat) = label (output (w ^^^ 4).toNat) :=
  PEqualNP.Outside.L_meta_25549.main_aux
