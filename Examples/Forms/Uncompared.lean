namespace Forms.Uncompared

structure Shift where
  apply : Nat → Nat

def shift (n : Nat) : Shift := ⟨fun x => x * 2 + n⟩

theorem shift_zero (n : Nat) : (shift n).apply 0 = n := by simp [shift]

end Forms.Uncompared
