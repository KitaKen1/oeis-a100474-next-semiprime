# OEIS A100474: the next semiprime

This repository contains a completed Lean formalization of the **exact
`next_semiprime` target** registered in
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/OEIS/100474.lean).

**Try it in Lean4Web:**
[Open the standalone proof in Lean4Web](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Foeis-a100474-next-semiprime%2Frefs%2Fheads%2Fmain%2Flean4web%2FOeisA100474NextSemiprimeLean4Web.lean)

The sequence is defined by

```text
a(0) = 0,
a(1) = 1,
a(n + 2) = (product of a consecutive block of primes) - a(n + 1).
```

The Formal Conjectures question asks for the first semiprime term after
`a(11)`.  The proposed answer is the term at index `36`:

```text
a(36) =
3852669607062814427999374038085094563026983841699038416757537720951140990693348082633155462564082456461927363575765861495986901576629
```

with factorization

```text
a(36) = 251 ×
15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356879.
```

The second factor has 131 digits and is prime.

## Formal Conjectures target

The file in `lean/` mirrors the definitions from Formal Conjectures at a pinned
commit and fills the answer with the explicit 133-digit value. The answer is
written directly as a numeral rather than through an auxiliary name:

```lean
theorem next_semiprime :
    answer(3852669607062814427999374038085094563026983841699038416757537720951140990693348082633155462564082456461927363575765861495986901576629) =
      a (sInf {n : ℕ | 11 < n ∧ (a n).IsSemiprime}) := by
  rw [least_semiprime_index, a_36]
```

Here `answer(...)` has type `ℕ`, because `next_semiprime` asks for a numerical
value.  `answer(True)` or `answer(False)` applies instead to the separate
yes/no theorem `OeisA100474.conjecture`.

## Mathematical Explanation (AI generated)

The proof has five layers:

1. certify the first 665 primes as a finite table and relate it to `Nat.nth`;
2. evaluate the recurrence sequentially from `a(0)` through `a(36)`;
3. exclude every index `12 ≤ n ≤ 35` using explicit three-factor decompositions;
4. prove the 131-digit cofactor prime with a recursive Lucas certificate, then
   prove `a(36) = 251 × p` is semiprime;
5. prove that `36` is the least qualifying index and conclude the exact `sInf`
   statement.

All finite computations are recorded through kernel-checkable Lean proofs.
The first 665 primes are certified in small `Nat.count` chunks with explicit
composite-factor witnesses, and the Lucas modular checks use verified
square-and-multiply traces normalized by `norm_num`. Neither project uses
`native_decide`, and both variants contain no `sorry` declarations.

## Files

| Directory | Lean version | Purpose |
|---|---:|---|
| `lean/` | `v4.27.0` | Exact Formal Conjectures target plus split kernel certificates, pinned to commit `638da20e...` |
| `lean4web/` | `v4.34.0-rc1` | Single-file standalone current-Mathlib version for Lean4Web |

The pinned Formal Conjectures project splits the first-665-primes certificate
into small modules to keep compilation memory bounded. The Lean4Web directory
bundles the same certificates into one loadable Lean file.

## Verification

Formal Conjectures version:

```bash
cd lean
lake update
lake exe cache get
lake build
```

Standalone mathlib / Lean4Web version:

```bash
cd lean4web
lake update
lake exe cache get
lake build
```

Both projects pass a warning-as-error build and include an axiom audit:

```bash
lake --wfail build
```

The final `#print axioms` output is

```text
[propext, Classical.choice, Quot.sound]
```

It contains no `sorryAx`, `Lean.trustCompiler`, or `Lean.ofReduceBool`.

## Status boundary

What this repository targets:

```text
The first semiprime term after a(11) is a(36), with the explicit value above.
```

What remains outside this repository:

```text
After a(2) = 5, does the sequence contain another prime term?
```

That is the separate theorem `OeisA100474.conjecture`.  Solving
`next_semiprime` does not solve it, so it must remain `research open`.

## Sources

- [OEIS A100474](https://oeis.org/A100474)
- [Formal Conjectures: `OEIS/100474.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/OEIS/100474.lean)
- [Repository layout used as a model](https://github.com/KitaKen1/erdos-361-asymptotic)

## AI Usage Disclosure

This formalization is assisted by ChatGPT 5.6 sol and Codex GPT 5.6 sol with
xhigh reasoning.
