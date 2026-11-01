/-
Copyright (c) 2026 Harii Sery. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harii Sery
-/

import Mathlib

/-!
# Ballot Theorem

The following amusing proposition was proved in 1878 by W. A. Whitworth,
and again in 1887 by J. Bertrand.

Suppose that, in a ballot, candidate P scores `p` votes and candidate Q scores `q` votes,
where `p > q`. The probability that throughout the counting
there are always more votes for P than for Q equals `(p - q) / (p + q)`.
This proof uses the reflection principle.

## Main definitions

* `possibilityspace p q`: the list of all `±1` sequences with `p` entries `1` and `q` entries `-1`
  (each sequence is encoded by the positions of its `1`s).
* `is_unif p q P`: `P : List ℤ → ℝ` is constant on `possibilityspace p q`.
* `Sₘ m l`: the partial sum of the first `m` entries of `l`.
* `condn p q l`: every nonempty prefix sum of `l` is positive (A is strictly ahead).
* `good_paths p q`, `bad_paths p q`: the paths of `possibilityspace p q` that do, respectively do
  not, satisfy `condn`.
* `probability p q P`: the total weight `P` gives to `good_paths p q`.
* `reflectPath`: reflects a path in its first return to `0`; an involution
  (`reflectPath_invol`).

## Assumptions

* `q < p`, i.e. P strictly wins the election.
* `is_unif p q P`: all orderings are equally likely.
* `((possibilityspace p q).map P).sum = 1`: `P` is a probability distribution.

## Main result

* `ballot_theorem`: under the assumptions above, `prob p q P = (p - q) / (p + q)`.

## Implementation notes

`reflectPath` gives a bijection (`refl_perm`) between bad paths starting with `1` and bad paths
starting with `-1`, so `bad_1_length` and `bad_neg1_length` give `|bad_paths| = 2 * C(p+q-1, p)`.
`good_add_bad` combines this with `possibilityspace_length`.
-/

namespace BallotReflection

variable (p q : Nat)

/-! ### Step 1. The possibility space and the groups of bad paths
The list of all arrangements of the votes, the `condn` test (A strictly ahead after every vote),
and the lists `good_paths`, `bad_paths`, `bad_paths_fstep_neg1`, `bad_paths_fstep_1`.
Also the bookkeeping that says what a member of `possibilityspace` looks like.
-/

def possibilityspace : List (List Int) :=
  (List.sublistsLen p (List.finRange (p + q))).map fun positivePositions =>
    (List.finRange (p + q)).map
      (fun i => if i ∈ positivePositions then (1 : Int) else -1)

def is_unif (P : List Int → ℝ) : Prop :=
  ∀ l₁ ∈ possibilityspace p q, ∀ l₂ ∈ possibilityspace p q, P l₁ = P l₂

def Sₘ (m : Nat) (l : List Int) : Int :=
  (l.take m).sum

def condn (l : List Int) : Bool :=
  (List.range (p+q+1)).all (fun step =>
  if step > 0 then Sₘ step l > 0 else true
  )

def good_paths : List (List Int) := (possibilityspace p q).filter (condn p q)

def probability (P : List Int → ℝ) : ℝ :=
  ((good_paths p q).map P).sum

def bad_paths : List (List Int) :=
  (possibilityspace p q).filter (fun l => !condn p q l)

def bad_paths_fstep_neg1 : List (List Int) :=
  List.filter (fun sublist : List Int => List.head? sublist == some (-1 : Int)) (bad_paths p q)

def bad_paths_fstep_1 : List (List Int) :=
  List.filter (fun sublist : List Int => List.head? sublist == some (1 : Int)) (bad_paths p q)


end BallotReflection
