import Mathlib

#eval Lean.versionString

/- Lean4Web does not import the Formal Conjectures `answer(...)` elaborator.
For this standalone target file, the notation has its ordinary identity
behavior. -/
macro "answer(" value:term ")" : term => `($value)

/-!
# OEIS A100474: standalone Lean4Web target

This file reproduces the definitions in the current Formal Conjectures file
`FormalConjectures/OEIS/100474.lean` and mirrors the same open
`next_semiprime` target with the explicit answer written directly in the final
theorem.  This file uses Mathlib's `Nat.IsSemiprime`, which is available in the
current Lean4Web release.

This is a target-aligned scaffold, not yet a completed proof.
-/

namespace OeisA100474NextSemiprimeLean4Web

noncomputable section

/-- The `n`-th triangular number, matching the Formal Conjectures definition. -/
def triangular (n : ℕ) : ℕ := n * (n + 1) / 2

/-- The primary sequence, copied exactly from the Formal Conjectures target. -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    (Finset.Ico (triangular (n + 1) - 1) (triangular (n + 2) - 1)).prod
        (Nat.nth Nat.Prime) -
      a (n + 1)

/-- The proposed least index greater than `11` whose sequence value is semiprime. -/
def nextSemiprimeIndex : ℕ := 36

/-- The explicit proposed answer to the Formal Conjectures target. -/
def nextSemiprimeValue : ℕ :=
  3852669607062814427999374038085094563026983841699038416757537720951140990693348082633155462564082456461927363575765861495986901576629

/-- The 131-digit prime cofactor of `nextSemiprimeValue`. -/
def largePrimeFactor : ℕ :=
  15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356879

/-- Exact arithmetic factorization of the proposed answer. -/
theorem nextSemiprimeValue_factorization :
    nextSemiprimeValue = 251 * largePrimeFactor := by
  norm_num [nextSemiprimeValue, largePrimeFactor]

/-- Certificate obligation: evaluate the recurrence at index `36`. -/
theorem a_36_value : a nextSemiprimeIndex = nextSemiprimeValue := by
  sorry

/-- Certificate obligation: the 131-digit cofactor is prime. -/
theorem largePrimeFactor_prime : largePrimeFactor.Prime := by
  sorry

/-- Certificate obligation: the value at index `36` is semiprime. -/
theorem a_36_semiprime : (a nextSemiprimeIndex).IsSemiprime := by
  sorry

/-- Certificate obligation: all indices strictly between `11` and `36` are excluded. -/
theorem no_semiprime_before_36 :
    ∀ n : ℕ, 11 < n → n < nextSemiprimeIndex → ¬(a n).IsSemiprime := by
  sorry

/-- The least qualifying index in the exact target set is `36`. -/
theorem least_semiprime_index :
    sInf {n : ℕ | 11 < n ∧ (a n).IsSemiprime} = nextSemiprimeIndex := by
  sorry

/-- Exact Formal Conjectures target with the explicit 133-digit answer. -/
theorem next_semiprime :
    answer(3852669607062814427999374038085094563026983841699038416757537720951140990693348082633155462564082456461927363575765861495986901576629) =
      a (sInf {n : ℕ | 11 < n ∧ (a n).IsSemiprime}) := by
  rw [least_semiprime_index, a_36_value]
  rfl

#print axioms next_semiprime

end

end OeisA100474NextSemiprimeLean4Web
