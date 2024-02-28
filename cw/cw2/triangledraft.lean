import Mathlib.Tactic

variable (n : ℕ)

def n_set : Finset ℕ := Finset.range n

def D₃ :
/- inductive type Dihedral Group n-/

import Mathlib.Tactic

variable (n : ℕ)

def N7 := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ

def subset_max_N7 (n : ℕ) : set (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  { x | let (a1, a2, a3, a4, a5, a6, a7) := x
         a1 ≤ n ∧ a2 ≤ n ∧ a3 ≤ n ∧ a4 ≤ n ∧ a5 ≤ n ∧ a6 ≤ n ∧ a7 ≤ n }


def subset_max_N7 (n : ℕ) : Set (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  { x | ∀ i ∈ Finset.range 7, (x.nth i).get_or_else 0 ≤ n }
def subset_max_N7 (n : ℕ) : Set N7 :=
  { x | ∀ i : Fin 7, x.nth i < n }

import Mathlib.Tactic

variable (a1 a2 a3 a4 a5 a6 a7 : ℕ )
variable (n : ℕ)
-- Define a predicate to check if the list contains elements a1 through a7 and the maximum is less than 7
def valid_list (l : List ℕ) : Prop :=
  l = [a1, a2, a3, a4, a5, a6, a7] ∧ ∀ x ∈ l, x < n

-- Define the set with the combined condition
def mySet : Set (List ℕ) :=
  { lst | valid_list lst }

  import Mathlib.Tactic

variable (n : ℕ)

def n_set : Set ℕ := Finset.range n

def n7 := n_set (n) × n_set (n) × n_set (n) × n_set (n) ×  n_set (n) × n_set (n) × n_set (n)

def permute_function (x : n7) :

structure pattern where
c1 : ℕ
c2 : ℕ
c3 : ℕ
c4 : ℕ
c5 : ℕ
c6 : ℕ
c7 : ℕ
bounded_components : List.maximum [c1, c2, c3, c4, c5, c6, c7] ≤ n

def N7 := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ

def subset_max_N7 (n : ℕ) : Set N7 :=
  { x | ∀ i ∈ Finset.range 7, x.nth i ≤ n }
