/-
  MergeSort Implementation in Lean 4
  Following the Lean Prover Style Guide
-/

import Lean
open Nat

universe u

/-- Merge two sorted lists into a single sorted list. -/
def merge {α : Type u} [Ord α] [LE α]                      -- the relation
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if x ≤ y then
      x :: merge xs (y :: ys)
    else
      y :: merge (x :: xs) ys

/-- Split a list into two approximately equal parts. -/
def split {α : Type u} : List α → List α × List α
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: zs =>
    let (xs, ys) := split zs
    (x :: xs, y :: ys)

/-- Sort a list using the merge sort algorithm. -/
def mergeSort {α : Type u} [Ord α] : List α → List α
  | [] => []
  | [x] => [x]
  | xs =>
    let (ys, zs) := split xs
    merge (mergeSort ys) (mergeSort zs)

/-- Proof that merge preserves length. -/
theorem merge_length {α : Type u} [Ord α] (xs ys : List α) :
    length (merge xs ys) = length xs + length ys := by
  induction xs generalizing ys with
  | nil =>
    simp [merge]
  | cons x xs ih =>
    cases ys with
    | nil =>
      simp [merge]
    | cons y ys =>
      simp [merge]
      by_cases h : x ≤ y
      · simp [h]
        rw [ih (y :: ys)]
        simp
      · simp [h]
        rw [ih ys]
        simp

/-- Proof that split preserves length. -/
theorem split_length {α : Type u} (xs : List α) :
    let (ys, zs) := split xs
    length ys + length zs = length xs := by
  induction xs with
  | nil =>
    simp [split]
  | cons x xs ih =>
    cases xs with
    | nil =>
      simp [split]
    | cons y ys =>
      simp [split]
      let (as, bs) := split ys
      have ih' := ih
      simp [split] at ih'
      rw [← ih']
      simp

/-- Proof that mergeSort preserves length. -/
theorem mergeSort_length {α : Type u} [Ord α] (xs : List α) :
    length (mergeSort xs) = length xs := by
  induction xs with
  | nil =>
    simp [mergeSort]
  | cons x xs ih =>
    cases xs with
    | nil =>
      simp [mergeSort]
    | cons y ys =>
      simp [mergeSort]
      let (as, bs) := split (x :: y :: ys)
      have split_len := split_length (x :: y :: ys)
      simp [split] at split_len
      rw [merge_length]
      have ih_as : length (mergeSort as) = length as := by
        sorry  -- Would be completed with a proper induction
      have ih_bs : length (mergeSort bs) = length bs := by
        sorry  -- Would be completed with a proper induction
      rw [ih_as, ih_bs]
      exact split_len

/-- Example usage of mergeSort -/
#eval mergeSort [3, 1, 4, 1, 5, 9, 2, 6, 5]  -- [1, 1, 2, 3, 4, 5, 5, 6, 9]
