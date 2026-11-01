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

lemma possibilityspace_length :
  (possibilityspace p q).length = (p + q).choose p := by
  simp [possibilityspace]

lemma sublist_eq_filter {α : Type} [DecidableEq α] {pos L : List α}
      (h : pos.Sublist L) : L.Nodup → L.filter (fun a => decide (a ∈ pos)) = pos := by
    induction h with
    | slnil =>
        intro _
        simp
    | @cons l₁ l₂ a h ih =>
        intro hL
        have ha : a ∉ l₂ := (List.nodup_cons.mp hL).1
        have hl2 : l₂.Nodup := (List.nodup_cons.mp hL).2
        have hanot : a ∉ l₁ := fun hm => ha (h.subset hm)
        rw [List.filter_cons_of_neg]
        · exact ih hl2
        · simpa using hanot
    | @cons_cons l₁ l₂ a h ih =>
        intro hL
        have ha : a ∉ l₂ := (List.nodup_cons.mp hL).1
        have hl2 : l₂.Nodup := (List.nodup_cons.mp hL).2
        have hcongr : l₂.filter (fun x => decide (x ∈ a :: l₁))
            = l₂.filter (fun x => decide (x ∈ l₁)) := by
          apply List.filter_congr
          intro x hx
          have hxa : x ≠ a := fun e => ha (by rw [← e]; exact hx)
          simp [hxa]
        rw [List.filter_cons_of_pos]
        · rw [hcongr, ih hl2]
        · simp

lemma sum_len_count (l : List Int) (h : ∀ x ∈ l, x = 1 ∨ x = -1) :
      l.sum + l.length = 2 * (l.count 1 : Int) := by
    induction l with
    | nil => simp
    | cons a l ih =>
        have ha := h a (by simp)
        have ih' := ih (fun x hx => h x (by simp [hx]))
        rcases ha with rfl | rfl <;> simp <;> omega

lemma count_map_eq_countP {α : Type} (f : α → Int) (L : List α) :
      (L.map f).count 1 = L.countP (fun a => f a == 1) := by
    induction L with
    | nil => simp
    | cons a L ih =>
        simp only [List.map_cons, List.count_cons, List.countP_cons]
        by_cases h : f a == 1 <;> simp [h, ih]

lemma mem_iff_of_ite {n : ℕ} {pos₁ pos₂ : List (Fin n)} {i : Fin n}
    (h : (if i ∈ pos₁ then (1 : Int) else -1) = (if i ∈ pos₂ then (1 : Int) else -1)) :
    i ∈ pos₁ ↔ i ∈ pos₂ := by
  by_cases h1 : i ∈ pos₁ <;> by_cases h2 : i ∈ pos₂ <;> simp_all

lemma possibilityspace_nodup : (possibilityspace p q).Nodup := by
  unfold possibilityspace
  have hF : (List.finRange (p + q)).Nodup := List.nodup_finRange _
  have hnd : (List.sublistsLen p (List.finRange (p + q))).Nodup :=
    List.nodup_sublistsLen p hF
  refine List.Nodup.map_on ?_ hnd
  intro pos₁ h₁ pos₂ h₂ heq
  have e := List.map_inj_left.mp heq
  have s₁ := (List.mem_sublistsLen.mp h₁).1
  have s₂ := (List.mem_sublistsLen.mp h₂).1
  calc
    pos₁ = (List.finRange (p + q)).filter (fun a => decide (a ∈ pos₁)) :=
      (sublist_eq_filter s₁ hF).symm
    _ = (List.finRange (p + q)).filter (fun a => decide (a ∈ pos₂)) := by
      apply List.filter_congr
      intro i hi
      have hi' := mem_iff_of_ite (e i hi)
      simp only [hi']
    _ = pos₂ := sublist_eq_filter s₂ hF

lemma ps_props {l : List Int} (hl : l ∈ possibilityspace p q) :
  l.length = p + q ∧ (∀ x ∈ l, x = 1 ∨ x = -1) ∧ l.sum = (p : Int) - q := by
  simp only [possibilityspace, List.mem_map, List.mem_sublistsLen] at hl
  obtain ⟨pos, ⟨hsub, hlen⟩, rfl⟩ := hl
  have hF : (List.finRange (p + q)).Nodup := List.nodup_finRange _
  refine ⟨by simp, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨i, _, rfl⟩ := hx
    by_cases hi : i ∈ pos <;> simp [hi]
  · have hsum_formula (xs : List (Fin (p + q))) :
        (xs.map (fun i => if i ∈ pos then (1 : Int) else -1)).sum
          = 2 * xs.countP (fun i => decide (i ∈ pos)) - xs.length := by
      induction xs with
      | nil => simp
      | cons i xs ih =>
          by_cases hi : i ∈ pos <;> simp [hi, ih] <;> omega
    have hcount : (List.finRange (p + q)).countP (fun i => decide (i ∈ pos)) = p := by
      rw [List.countP_eq_length_filter, sublist_eq_filter hsub hF]
      exact hlen
    rw [hsum_formula, hcount]
    simp only [List.length_finRange]
    push_cast
    ring

lemma ps_of_props {l : List Int} (hlen : l.length = p + q)
  (h1 : ∀ x ∈ l, x = 1 ∨ x = -1) (hsum : l.sum = (p : Int) - q) :
  l ∈ possibilityspace p q := by
  have hcnt : l.count 1 = p := by
    have hcount := sum_len_count l h1
    omega
  let g : Fin (p + q) → Int := fun i => l[i.val]'(by have := i.isLt; omega)
  have hgdef : ∀ i : Fin (p + q), g i = l[i.val]'(by have := i.isLt; omega) := by
    intro i
    rfl
  have hg : ∀ i, g i = 1 ∨ g i = -1 := by
    intro i
    rw [hgdef]
    exact h1 _ (by simp)
  have hmap : (List.finRange (p + q)).map g = l := by
    apply List.ext_getElem
    · simp [hlen]
    · intro j hj1 hj2
      simp only [List.getElem_map]
      rw [hgdef]
      simp
  have hc : (List.finRange (p + q)).countP (fun i => g i == 1) = p := by
    have h := count_map_eq_countP g (List.finRange (p + q))
    rw [hmap, hcnt] at h
    exact h.symm
  simp only [possibilityspace, List.mem_map, List.mem_sublistsLen]
  refine ⟨(List.finRange (p + q)).filter (fun i => g i == 1), ?_, ?_⟩
  · constructor
    · exact List.filter_sublist
    · rw [← List.countP_eq_length_filter]
      exact hc
  · rw [← hmap]
    apply List.map_congr_left
    intro i _
    by_cases h : g i = 1
    · simp [h]
    · have h' : g i = -1 := (hg i).resolve_left h
      simp [h']


end BallotReflection
