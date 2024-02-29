import Mathlib.Tactic

inductive MyD₃
  | r : Fin 3 → MyD₃
  | sr: Fin 3 → MyD₃
deriving instance DecidableEq

for MyD₃
namespace MyD₃

def D₃GroupLaw : MyD₃ → MyD₃ → MyD₃
  | r i, r j => r ((i + j) % 3)
  | r i, sr j => sr ((j - i) % 3)
  | sr i, r j => sr ((i + j) % 3)
  | sr i, sr j => r ((j - i) % 3)

def D₃id : MyD₃ := r 0

def D₃inv : MyD₃ → MyD₃
  | r i => r ((3-i) % 3)
  | sr i => sr i

instance : Group (MyD₃) where
  mul := D₃GroupLaw
  mul_assoc := by sorry
  one := D₃id
  one_mul := by sorry
  mul_one := by sorry
  inv := D₃inv
  mul_left_inv := by sorry
