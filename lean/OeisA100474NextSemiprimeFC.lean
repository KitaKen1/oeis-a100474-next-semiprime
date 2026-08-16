import FormalConjectures.OEIS.«100474»

/-!
# OEIS A100474: exact Formal Conjectures `next_semiprime` target

This file imports the current Formal Conjectures definitions and specializes
the answer in `OeisA100474.next_semiprime` to the explicit value of `a(36)`.
The numeral is written directly in the final theorem.

This is a target-aligned scaffold.  The four named proof obligations below must
be replaced by kernel-checked certificate proofs before the target can be
claimed as solved.
-/

namespace OeisA100474NextSemiprime

noncomputable section

open OeisA100474

/-- The proposed least index greater than `11` whose sequence value is semiprime. -/
def nextSemiprimeIndex : ℕ := 36

/-- The explicit value of `OeisA100474.a 36`. -/
def nextSemiprimeValue : ℕ :=
  3852669607062814427999374038085094563026983841699038416757537720951140990693348082633155462564082456461927363575765861495986901576629

/-- The 131-digit prime cofactor of `nextSemiprimeValue`. -/
def largePrimeFactor : ℕ :=
  15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356879

/-- Exact arithmetic factorization of the proposed answer. -/
theorem nextSemiprimeValue_factorization :
    nextSemiprimeValue = 251 * largePrimeFactor := by
  norm_num [nextSemiprimeValue, largePrimeFactor]

/-- Certificate obligation: evaluate the Formal Conjectures recurrence at index `36`. -/
theorem a_36_value :
    OeisA100474.a nextSemiprimeIndex = nextSemiprimeValue := by
  sorry

/-- Certificate obligation: the 131-digit cofactor is prime. -/
theorem largePrimeFactor_prime : largePrimeFactor.Prime := by
  sorry

/-- Certificate obligation: the value at index `36` is semiprime. -/
theorem a_36_semiprime :
    (OeisA100474.a nextSemiprimeIndex).IsSemiprime := by
  sorry

/-- Certificate obligation: all indices strictly between `11` and `36` are excluded. -/
theorem no_semiprime_before_36 :
    ∀ n : ℕ, 11 < n → n < nextSemiprimeIndex →
      ¬(OeisA100474.a n).IsSemiprime := by
  sorry

/-- The least qualifying index in the exact set used by Formal Conjectures is `36`. -/
theorem least_semiprime_index :
    sInf {n : ℕ | 11 < n ∧ (OeisA100474.a n).IsSemiprime} = nextSemiprimeIndex := by
  sorry

/-- Exact Formal Conjectures target with the explicit 133-digit answer. -/
theorem next_semiprime :
    answer(3852669607062814427999374038085094563026983841699038416757537720951140990693348082633155462564082456461927363575765861495986901576629) =
      a (sInf {n : ℕ | 11 < n ∧ (a n).IsSemiprime}) := by
  rw [least_semiprime_index, a_36_value]
  rfl

#print axioms next_semiprime

end

end OeisA100474NextSemiprime
