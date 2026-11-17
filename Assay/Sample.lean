import Plausible

/-!
Generators that `#assay` puts in place of plausible's defaults, and the parts of the generator it
writes for a recursive type.

plausible's `Char` generator draws code points below the sample size, so it never produces a
character outside the Basic Multilingual Plane. Specifications about UTF-8 and UTF-16 widths need
characters of every width, so this generator mixes ASCII with two-, three- and four-byte
characters.
-/

open Plausible

namespace Assay

/-- Characters of every UTF-8 width and of both UTF-16 widths, with the code points at each boundary
between widths. -/
def wideChars : List Char :=
  " aZ09\n\r\t".toList ++ ['é', 'ß', 'Ω', 'あ', '漢', '€', '😀', '𝔸', '𠀋'] ++
    [Char.ofNat 0x7F, Char.ofNat 0x80, Char.ofNat 0x7FF, Char.ofNat 0x800, Char.ofNat 0xFFFF,
      Char.ofNat 0x10000, Char.ofNat 0x10FFFF]

instance (priority := high) charArbitrary : Arbitrary Char where
  arbitrary := do
    let i ← Gen.choose Nat 0 (wideChars.length - 1) (by decide)
    return wideChars[i.val]!

/-- How many constructors deep a generator goes on at size 0 before it fails. A constructor whose
recursive fields are all containers is built with the containers empty, so this bounds only a chain
through fields such as `Option T`. -/
def floorFuel : Nat := 8

/-- The generator of a recursive type as the fields of its constructors see it: `gen` with the fuel
left. At a positive size the fuel starts over, because the size shrinks on the way to every field. -/
def Gen.step {α : Type} (gen : Nat → Gen α) (fuel : Nat) : Gen α := do
  if (← Gen.getSize) != 0 then gen floorFuel
  else match fuel with
    | 0 => throw Gen.genericFailure
    | fuel + 1 => gen fuel

/-- Runs `x` again, on other random numbers, each time it fails, at most `n` more times. -/
def Gen.retry {α : Type} (n : Nat) (x : Gen α) : Gen α :=
  match n with
  | 0 => x
  | n + 1 => tryCatch x fun _ => do
    let _ ← Gen.chooseAny Bool
    Gen.retry n x

/-- A constructor field whose type is the recursive type, in a constructor with `k` recursive
fields: the size left after this constructor is split among them. -/
def Gen.direct {α : Type} (k : Nat) (x : Gen α) : Gen α :=
  Gen.resize (fun size => (size - 1) / k) x

/-- A constructor field whose type contains the recursive type (`List T`, `Option T`, …): the
container and the values in it are drawn at the square root of the size, which keeps the number of
values in the whole tree small. At size 0 a container that came out non-empty and
ran out of fuel is drawn again. -/
def Gen.nested {α : Type} (x : Gen α) : Gen α := do
  if (← Gen.getSize) == 0 then Gen.retry floorFuel x
  else Gen.resize (fun size => min size.sqrt (size - 1)) x

/-- Picks a constructor of a recursive type: one of `leaves` (no recursive field) at size 0, and
otherwise any, a recursive one `size + 1` times as often as a leaf. -/
def Gen.pick {α : Type} (leaves recursive : Array (Gen α)) : Gen α := do
  let size ← Gen.getSize
  let weight := if size == 0 && leaves.size != 0 then 0 else size + 1
  let total := leaves.size + recursive.size * weight
  if total == 0 then throw Gen.genericFailure
  let i := (← Gen.choose Nat 0 (total - 1) (by omega)).val
  if h : i < leaves.size then leaves[i]
  else if h : (i - leaves.size) / weight < recursive.size then recursive[(i - leaves.size) / weight]
  else throw Gen.genericFailure

end Assay
