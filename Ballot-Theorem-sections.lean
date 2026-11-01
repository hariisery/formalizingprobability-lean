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

/-! ### Step 2. Split the bad paths by their first step
Every bad path starts with `1` or `-1`, and these two groups do not overlap.
-/

lemma bad_split : (bad_paths p q).length =
  (bad_paths_fstep_1 p q).length + (bad_paths_fstep_neg1 p q).length := by
  have hheads : ∀ path ∈ bad_paths p q,
      path.head? = some (1 : Int) ∨ path.head? = some (-1 : Int) := by
    intro path hpath
    have hcond : condn p q path = false := by
      have h := (List.mem_filter.mp hpath).2
      simpa using h
    have hposs := (List.mem_filter.mp hpath).1
    rcases (by simpa [possibilityspace] using hposs) with ⟨positions, _, rfl⟩
    by_cases hzero : p + q = 0
    · have hp : p = 0 := by omega
      have hq : q = 0 := by omega
      subst p
      subst q
      simp [condn] at hcond
    · have hhead : (List.finRange (p + q)).head? ≠ none := by
        intro hnil
        have hnil' : List.finRange (p + q) = [] := List.head?_eq_none_iff.mp hnil
        have : (List.finRange (p + q)).length = 0 := by simp [hnil']
        simp only [List.length_finRange] at this
        omega
      cases hfirst : (List.finRange (p + q)).head? with
      | none => exact (hhead hfirst).elim
      | some i =>
        rw [List.head?_map, hfirst]
        by_cases hi : i ∈ positions <;> simp [hi]
  have hfilters :
      List.filter (fun path : List Int => !(path.head? == some (1 : Int))) (bad_paths p q)
        = bad_paths_fstep_neg1 p q := by
    unfold bad_paths_fstep_neg1
    apply List.filter_congr
    intro path hpath
    rcases hheads path hpath with h | h <;> simp [h]
  have hperm := List.filter_append_perm
    (fun path : List Int => path.head? == some (1 : Int)) (bad_paths p q)
  rw [hfilters] at hperm
  simpa [bad_paths_fstep_1] using hperm.length_eq.symm

/-! ### Step 3. Follow the running total until it first hits 0, then flip
A bad path touches 0 (`crosses_zero`, `returns_origin`, `hit_down`, `hit_of_bad`).
`reflectPath` flips every step up to the first touch of 0; flipping twice gives the path back.
-/

lemma crosses_zero (xs : List Int) (s : Int)
    (hs : s < 0)
    (hfinal : 0 < s + xs.sum)
    (hsteps : ∀ x ∈ xs, x = 1 ∨ x = -1) :
    ∃ n ≤ xs.length, s + (xs.take n).sum = 0 := by
    induction xs generalizing s with
    | nil =>
    simp at hfinal
    omega
    | cons x xs ih =>
    have hx : x = 1 ∨ x = -1 := hsteps x (by simp)
    by_cases hz : s + x = 0
    · use 1; simp[hz]
    · have hst : ∀ x ∈ xs, x = 1 ∨ x = -1 := fun x hu => hsteps x (by simp [hu])
      have hsn : s + x < 0 := by
        rcases hx with rfl | rfl <;> omega
      have hfinal' : 0 < s + (x + xs.sum) := by simpa using hfinal
      have hfn : 0 < (s + x) + xs.sum := by omega
      obtain ⟨n, hn1, hn2⟩ := ih (s + x) hsn hfn hst
      use n+1; simp [hn1]; omega

theorem returns_origin (path : List Int)
    (hpath : path ∈ bad_paths_fstep_neg1 p q)
    (hqp : q < p) :
    ∃ n, 0 < n ∧ Sₘ n path = 0 := by
  have hposs : path ∈ possibilityspace p q :=
    (List.mem_filter.mp (List.mem_filter.mp hpath).1).1
  have hstart : path.head? = some (-1 : Int) := by
    simpa using (List.mem_filter.mp hpath).2
  obtain ⟨-, hsteps, hsum⟩ := ps_props p q hposs
  have hfinal : 0 < path.sum := by rw [hsum]; omega
  cases path with
  | nil => simp at hstart
  | cons first rest =>
    have hfirst : first = -1 := by simpa using hstart
    subst first
    have hfinal' : 0 < (-1 : Int) + rest.sum := by simpa using hfinal
    have hsteps' : ∀ x ∈ rest, x = 1 ∨ x = -1 := by
      intro x hx
      exact hsteps x (by simp [hx])
    obtain ⟨n, hnlen, hnzero⟩ :=
      crosses_zero rest (-1) (by decide) hfinal' hsteps'
    refine ⟨n + 1, by omega, ?_⟩
    simpa [Sₘ] using hnzero

lemma condn_false_of_head {l : List Int} (hhead : l.head? = some (-1))
    (hpq : 1 ≤ p + q) : condn p q l = false := by
  cases l with
  | nil => simp at hhead
  | cons a t =>
      have ha : a = -1 := by simpa using hhead
      subst a
      rw [Bool.eq_false_iff]
      intro hcond
      unfold condn at hcond
      rw [List.all_eq_true] at hcond
      have hstep := hcond 1 (List.mem_range.mpr (by omega))
      simp [Sₘ] at hstep

lemma exists_nonpos_prefix {l : List Int} (hc : condn p q l = false) :
    ∃ n, 0 < n ∧ n ≤ p + q ∧ (l.take n).sum ≤ 0 := by
  by_contra hno
  have hno' : ∀ n, 0 < n → n ≤ p + q → 0 < (l.take n).sum := by
    intro n hn hle
    by_contra hsum
    exact hno ⟨n, hn, hle, by omega⟩
  have hall : (List.range (p + q + 1)).all (fun step =>
      if step > 0 then Sₘ step l > 0 else true) = true := by
    rw [List.all_eq_true]
    intro step hstep
    have hstep' := List.mem_range.mp hstep
    by_cases hpos : 0 < step
    · have hsum := hno' step hpos (by omega)
      simpa [Sₘ, hpos] using hsum
    · simp [hpos]
  have htrue : condn p q l = true := by
    simpa [condn] using hall
  rw [htrue] at hc
  cases hc

lemma hit_down (xs : List Int) : ∀ (s : Int) (n : ℕ), 0 < s →
    (∀ x ∈ xs, x = 1 ∨ x = -1) → s + (xs.take n).sum ≤ 0 →
    ∃ k, 0 < k ∧ k ≤ xs.length ∧ s + (xs.take k).sum = 0 := by
  induction xs with
  | nil =>
      intro s n hs _ h
      simp at h
      omega
  | cons x xs ih =>
      intro s n hs hx h
      have hx' := hx x (by simp)
      cases n with
      | zero =>
          simp at h
          omega
      | succ n =>
          simp only [List.take_succ_cons, List.sum_cons] at h
          by_cases hz : s + x = 0
          · refine ⟨1, by omega, by simp, ?_⟩
            simpa using hz
          · have hpos : 0 < s + x := by
              rcases hx' with h' | h' <;> omega
            obtain ⟨k, hk0, hkle, hk⟩ :=
              ih (s + x) n hpos (fun y hy => hx y (by simp [hy])) (by omega)
            refine ⟨k + 1, by omega, ?_, ?_⟩
            · simp only [List.length_cons]
              omega
            · simpa [List.take_succ_cons, List.sum_cons, Int.add_assoc] using hk

lemma hit_of_bad (l : List Int) (h1 : ∀ x ∈ l, x = 1 ∨ x = -1) (hhead : l.head? = some 1)
    (n : ℕ) (hn : 0 < n) (hle : (l.take n).sum ≤ 0) :
    ∃ k, 0 < k ∧ k ≤ l.length ∧ (l.take k).sum = 0 := by
  cases l with
  | nil => simp at hhead
  | cons a t =>
      have ha : a = 1 := by simpa using hhead
      subst a
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have hle' : 1 + (t.take n').sum ≤ 0 := by
        simpa [List.take_succ_cons, List.sum_cons] using hle
      obtain ⟨k, hk0, hkle, hk⟩ :=
        hit_down t 1 n' (by omega) (fun x hx => h1 x (by simp [hx])) (by omega)
      refine ⟨k + 1, by omega, ?_, ?_⟩
      · simp only [List.length_cons]
        omega
      · simpa [List.take_succ_cons, List.sum_cons] using hk

def reflAux (s : Int) : List Int → List Int
  | [] => []
  | x :: xs =>
      if s + x = 0 then -x :: xs else -x :: reflAux (s + x) xs

def reflectPath (l : List Int) : List Int :=
  reflAux 0 l

def refl_bad_paths_fstep_neg1 : List (List Int) :=
  (bad_paths_fstep_neg1 p q).map reflectPath

lemma sum_map_neg (l : List Int) : (l.map (fun x => -x)).sum = -l.sum := by
    induction l with
    | nil => simp
    | cons a l ih =>
        simp only [List.map_cons, List.sum_cons, ih]
        omega

lemma reflAux_hit : ∀ (xs : List Int) (s : Int),
    (∃ n, 0 < n ∧ n ≤ xs.length ∧ s + (xs.take n).sum = 0) →
    ∃ k, 0 < k ∧ k ≤ xs.length ∧ s + (xs.take k).sum = 0 ∧
      reflAux s xs = (xs.take k).map (fun x => -x) ++ xs.drop k := by
  intro xs
  induction xs with
  | nil =>
      intro s h
      rcases h with ⟨n, hn, hle, hsum⟩
      simp at hle
      omega
  | cons x xs ih =>
      intro s h
      rcases h with ⟨n, hn, hle, hsum⟩
      by_cases hz : s + x = 0
      · refine ⟨1, by omega, by simp, ?_, ?_⟩
        · simp
          simpa using hz
        · simp [reflAux, hz]
      · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        have hsum' : (s + x) + (xs.take n').sum = 0 := by
          have hsum'' : s + (x + (xs.take n').sum) = 0 := by
            simpa [List.take_succ_cons, List.sum_cons] using hsum
          omega
        have hn' : 0 < n' := by
          by_contra hn0
          have : n' = 0 := by omega
          subst n'
          simp at hsum'
          exact hz (by omega)
        have hle' : n' ≤ xs.length := by
          simp only [List.length_cons] at hle
          omega
        obtain ⟨k, hk0, hkle, hksum, hkeq⟩ :=
          ih (s + x) ⟨n', hn', hle', hsum'⟩
        refine ⟨k + 1, by omega, ?_, ?_, ?_⟩
        · simp only [List.length_cons]
          omega
        · simpa [List.take_succ_cons, List.sum_cons, Int.add_assoc] using hksum
        · simp [reflAux, hz, hkeq, List.take_succ_cons, List.drop_succ_cons]

lemma reflAux_invol (s : Int) (xs : List Int) :
    reflAux (-s) (reflAux s xs) = xs := by
  induction xs generalizing s with
  | nil => simp [reflAux]
  | cons x xs ih =>
      by_cases hz : s + x = 0
      · have hzero : (-s) + (-x) = 0 := by omega
        simp [reflAux, hz, hzero]
      · have hfirst : reflAux s (x :: xs) = -x :: reflAux (s + x) xs := by
          simp [reflAux, hz]
        have hne : (-s) + (-x) ≠ 0 := by omega
        have hstate : (-s) + (-x) = -(s + x) := by omega
        calc
          reflAux (-s) (reflAux s (x :: xs))
              = reflAux (-s) (-x :: reflAux (s + x) xs) := by rw [hfirst]
          _ = x :: reflAux ((-s) + (-x)) (reflAux (s + x) xs) := by
                simp [reflAux, hne]
          _ = x :: reflAux (-(s + x)) (reflAux (s + x) xs) := by rw [hstate]
          _ = x :: xs := by rw [ih]

lemma reflectPath_invol (xs : List Int) : reflectPath (reflectPath xs) = xs := by
  simpa [reflectPath] using reflAux_invol 0 xs

lemma refl_head {l : List Int} {a : Int} (hs : l.head? = some a) (ha : a ≠ 0) :
    (reflectPath l).head? = some (-a) := by
  cases l with
  | nil => simp at hs
  | cons b t =>
      have hb : b = a := by simpa using hs
      subst b
      simp [reflectPath, reflAux, ha]

lemma refl_facts (m : List Int) (h1 : ∀ x ∈ m, x = 1 ∨ x = -1)
    (hit : ∃ n, 0 < n ∧ n ≤ m.length ∧ (m.take n).sum = 0) :
    (reflectPath m).length = m.length ∧ (∀ x ∈ reflectPath m, x = 1 ∨ x = -1) ∧
      (reflectPath m).sum = m.sum ∧
      ∃ k, 0 < k ∧ k ≤ m.length ∧ ((reflectPath m).take k).sum = 0 := by
  obtain ⟨k, hk0, hkle, hks, hke⟩ := reflAux_hit m 0 (by simpa using hit)
  have hke' : reflectPath m = (m.take k).map (fun x => -x) ++ m.drop k := hke
  have hks' : (m.take k).sum = 0 := by simpa using hks
  refine ⟨?_, ?_, ?_, k, hk0, hkle, ?_⟩
  · rw [hke']
    simp only [List.length_append, List.length_map, List.length_take, List.length_drop]
    omega
  · intro x hx
    rw [hke'] at hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      rcases h1 y (List.mem_of_mem_take hy) with h | h <;> simp [h]
    · exact h1 x (List.mem_of_mem_drop hx)
  · rw [hke', List.sum_append, sum_map_neg]
    have hsum : (m.take k).sum + (m.drop k).sum = m.sum := by
      rw [← List.sum_append, List.take_append_drop]
    omega
  · have htl : List.take k ((m.take k).map (fun x => -x) ++ m.drop k)
        = (m.take k).map (fun x => -x) :=
      List.take_left' (by simp [Nat.min_eq_left hkle])
    have hs0 : ((m.take k).map (fun x => -x)).sum = 0 := by
      rw [sum_map_neg]
      omega
    rw [hke', htl]
    exact hs0

/-! ### Step 4. The flip is a bijection between the two groups of bad paths
Flipping sends bad paths starting with `-1` to bad paths starting with `1`, and back,
so the two groups have the same size.
-/

lemma refl_mem_one (hqp : q < p) {m : List Int} (hm : m ∈ bad_paths_fstep_neg1 p q) :
  reflectPath m ∈ bad_paths_fstep_1 p q := by
  obtain ⟨hbad, hhead⟩ := List.mem_filter.mp hm
  have hps : m ∈ possibilityspace p q := (List.mem_filter.mp hbad).1
  have hs : m.head? = some (-1) := by simpa using hhead
  obtain ⟨hlen, h1, hsum⟩ := ps_props p q hps
  obtain ⟨n, hn0, hn⟩ := returns_origin p q m hm hqp
  have hn' : n ≤ m.length := by
    by_contra hgt
    have hlt : m.length < n := by omega
    have htk : m.take n = m := List.take_of_length_le (Nat.le_of_lt hlt)
    have hsum_zero : m.sum = 0 := by
      simpa [Sₘ, htk] using hn
    rw [hsum] at hsum_zero
    omega
  obtain ⟨hlen', h1', hsum', k, hk0, hkle, hSk⟩ :=
    refl_facts m h1 ⟨n, hn0, hn', by simpa [Sₘ] using hn⟩
  have hps' : reflectPath m ∈ possibilityspace p q :=
    ps_of_props p q (by omega) h1' (by omega)
  have hcf : condn p q (reflectPath m) = false := by
    rw [Bool.eq_false_iff]
    intro hc
    unfold condn at hc
    rw [List.all_eq_true] at hc
    have hstep := hc k (List.mem_range.mpr (by omega))
    simp [Sₘ, hSk, hk0] at hstep
  unfold bad_paths_fstep_1 bad_paths
  simp only [List.mem_filter]
  refine ⟨⟨hps', ?_⟩, ?_⟩
  · simp [hcf]
  · simpa using refl_head hs (by decide)

lemma refl_mem_neg (hqp : q < p) {l : List Int} (hl : l ∈ bad_paths_fstep_1 p q) :
  reflectPath l ∈ bad_paths_fstep_neg1 p q := by
  obtain ⟨hbad, hhead⟩ := List.mem_filter.mp hl
  have hps : l ∈ possibilityspace p q := (List.mem_filter.mp hbad).1
  have hnc : condn p q l = false := by simpa using (List.mem_filter.mp hbad).2
  have hs : l.head? = some 1 := by simpa using hhead
  obtain ⟨hlen, h1, hsum⟩ := ps_props p q hps
  obtain ⟨n, hn0, -, hn⟩ := exists_nonpos_prefix p q hnc
  obtain ⟨k, hk0, hkle, hk⟩ := hit_of_bad l h1 hs n hn0 hn
  obtain ⟨hlen', h1', hsum', -⟩ := refl_facts l h1 ⟨k, hk0, hkle, hk⟩
  have hps' : reflectPath l ∈ possibilityspace p q :=
    ps_of_props p q (by omega) h1' (by omega)
  have hs' : (reflectPath l).head? = some (-1) := by
    simpa using refl_head hs (by decide)
  unfold bad_paths_fstep_neg1 bad_paths
  simp only [List.mem_filter]
  refine ⟨⟨hps', ?_⟩, ?_⟩
  · simp [condn_false_of_head p q hs' (by omega)]
  · simpa using hs'

lemma refl_perm (hqp : q < p) :
  (refl_bad_paths_fstep_neg1 p q).Perm (bad_paths_fstep_1 p q) := by
  unfold refl_bad_paths_fstep_neg1
  have hnd0 : (possibilityspace p q).Nodup := possibilityspace_nodup p q
  have hnd_neg : (bad_paths_fstep_neg1 p q).Nodup := by
    unfold bad_paths_fstep_neg1 bad_paths
    exact (hnd0.filter _).filter _
  have hnd_one : (bad_paths_fstep_1 p q).Nodup := by
    unfold bad_paths_fstep_1 bad_paths
    exact (hnd0.filter _).filter _
  have hinj : Function.Injective reflectPath :=
    Function.LeftInverse.injective reflectPath_invol
  refine (List.perm_ext_iff_of_nodup (hnd_neg.map hinj) hnd_one).2 ?_
  intro l
  constructor
  · intro hl
    obtain ⟨m, hm, hml⟩ := List.mem_map.mp hl
    rw [← hml]
    exact refl_mem_one p q hqp hm
  · intro hl
    exact List.mem_map.mpr
      ⟨reflectPath l, refl_mem_neg p q hqp hl, reflectPath_invol l⟩

lemma bad_1_length (hpq : q < p) :
    (bad_paths_fstep_1 p q).length = (bad_paths_fstep_neg1 p q).length := by
    rw [← (refl_perm p q hpq).length_eq]
    simp [refl_bad_paths_fstep_neg1]

/-! ### Step 5. Count the `-1`-start paths and subtract them twice
There are `C(p+q-1, p)` paths starting with `-1`, all of them bad.
good paths = all paths - 2 * (bad paths starting with `-1`).
-/

lemma neg1_count (m n k : ℕ) (hm : m = n + 1) :
(((List.sublistsLen k (List.finRange m)).map
(fun pos => (List.finRange m).map
(fun i => if i ∈ pos then (1 : Int) else -1))).filter
(fun l => l.head? == some (-1))).length = n.choose k := by
  subst hm
  have hfr : List.finRange (n + 1) = 0 :: (List.finRange n).map Fin.succ := by
    exact List.finRange_succ
  have hpred : ∀ pos : List (Fin (n + 1)),
    (((List.finRange (n + 1)).map
    (fun i => if i ∈ pos then (1 : Int) else -1)).head? == some (-1))
    = decide ((0 : Fin (n + 1)) ∉ pos) := by
    intro pos
    rw [hfr]
    by_cases h : (0 : Fin (n + 1)) ∈ pos <;> simp [h]
  simp only [List.filter_map, List.length_map, Function.comp_def, hpred]
  rw [hfr]
  rcases k with _ | k
  · simp
  · have hA : List.filter (fun x => decide ((0 : Fin (n + 1)) ∉ x))
      (List.sublistsLen (k + 1) ((List.finRange n).map Fin.succ))
      = List.sublistsLen (k + 1) ((List.finRange n).map Fin.succ) := by
      apply List.filter_eq_self.mpr
      intro pos hpos
      have hsub := (List.mem_sublistsLen.mp hpos).1
      have h0 : (0 : Fin (n + 1)) ∉ pos := by
        intro h0
        have hmem := hsub.subset h0
        simp at hmem
      simp [h0]
    have hB : List.filter (fun x => decide ((0 : Fin (n + 1)) ∉ x))
      ((List.sublistsLen k ((List.finRange n).map Fin.succ)).map (List.cons 0)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro pos hpos
      obtain ⟨s, _, rfl⟩ := List.mem_map.mp hpos
      simp
    rw [List.sublistsLen_succ_cons]
    simp only [List.filter_append, List.length_append]
    rw [hA, hB]
    simp [List.length_sublistsLen]

lemma bad_neg1_length (hqp : q < p) (hp : 0 < p) :
(bad_paths_fstep_neg1 p q).length = (p + q - 1).choose p := by
  have hfilt : bad_paths_fstep_neg1 p q =
      (possibilityspace p q).filter (fun l => l.head? == some (-1)) := by
    unfold bad_paths_fstep_neg1 bad_paths
    rw [List.filter_filter]
    apply List.filter_congr
    intro l _
    by_cases h : l.head? = some (-1)
    · cases l with
      | nil => simp at h
      | cons a t =>
        have ha : a = -1 := by simpa using h
        subst a
        have hc := condn_false_of_head p q h (by omega)
        simp [h, hc]
    · have hb : (l.head? == some (-1)) = false := by simpa using h
      simp [hb]
  rw [hfilt]
  exact neg1_count (p + q) (p + q - 1) p (by omega)

lemma good_add_bad (hqp : q < p) (hp : 0 < p) :
    (good_paths p q).length + 2 * (p + q - 1).choose p = (p + q).choose p := by
    have h : (good_paths p q).length + (bad_paths p q).length
    = (possibilityspace p q).length := by
      simpa [good_paths, bad_paths] using
    (List.filter_append_perm (condn p q) (possibilityspace p q)).length_eq
    have := bad_split p q
    have := bad_1_length p q hqp
    have := bad_neg1_length p q hqp hp
    have := possibilityspace_length p q
    omega


end BallotReflection
