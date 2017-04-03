/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/

import ..algebra.order ..data.fin
open nat tactic

def and_of_map_aux (n : ℕ) (f : fin n → Prop) : Π k, k < n → Prop
| 0 h := f (fin.mk 0 h)
| (k + 1) h := (and_of_map_aux k (lt_of_succ_lt h)) ∧ f (fin.mk (k+1) h)

def and_of_map : Π {n : ℕ}, (fin n → Prop) → Prop
| 0 P := true
| (k+1) P := and_of_map_aux (k+1) P k (lt_succ_self _)


theorem and_of_map_aux_of_forall (n : ℕ) (P : fin n → Prop) (H : ∀ n : fin n, P n) : Π k, Π p : k < n, and_of_map_aux n P k p
| 0 p := H _
| (k+1) p := and.intro (by apply and_of_map_aux_of_forall) (H _)

theorem and_of_map_of_forall : Π {n : ℕ} {P : fin n → Prop} (H : ∀ k : fin n, P k), and_of_map P
| 0 P H := trivial
| (k+1) P H := and_of_map_aux_of_forall _ _ H _ _

lemma eq_of_ge_of_lt_succ {n k : ℕ} (h1 : k ≥ n) (h2 : k < n+1) : k = n := 
have n = k ∨ n < k, from nat.eq_or_lt_of_le h1,
or.elim this
 (suppose n = k, eq.symm this)
 (suppose n < k, have n+1 < n+1, from calc
   n+1 ≤ k   : succ_le_of_lt this
   ... < n+1 : h2,
  absurd this (lt_irrefl _))

lemma eq_zero_of_lt_one {n : ℕ} (Hn : n < 1) : n = 0 := 
eq_zero_of_le_zero (le_of_lt_succ Hn)

def fin_lower {n : ℕ} (v : fin (succ n)) (h : v^.val < n) : fin n := ⟨v^.val, h⟩

def fin_prop_lower {n : ℕ} (P : fin (succ n) → Prop) : fin n → Prop := λ v, P ⟨v^.val, lt_succ_of_lt v^.is_lt⟩

theorem of_fin_prop_lower (n : ℕ) (P : fin (succ n) → Prop) (v : fin (succ n)) (h : v^.val < n) 
        (hvp : fin_prop_lower P (fin_lower v h)) : P v := 
begin
 unfold fin_prop_lower at hvp, unfold fin_lower at hvp,
 dsimp at hvp,
 assert h' : v = {val := v^.val, is_lt := v^.is_lt}, 
 induction v,
 apply congr,
 reflexivity,
 reflexivity,
 rw h',
 apply hvp
end

theorem and_of_map_aux_lower {n : ℕ} {P : fin (succ n) → Prop}  (k) (h : k < n) 
        (h2 : and_of_map_aux (n+1) P k (lt_succ_of_lt h)) :
        and_of_map_aux n (fin_prop_lower P) k h := 
begin
 induction k,
 apply h2,
 unfold and_of_map_aux,
 split,
 apply ih_1,
 apply and.left h2,
 apply and.right h2
end

theorem and_of_map_lower {n : ℕ} {P : fin (succ n) → Prop} (H : and_of_map P) : and_of_map (fin_prop_lower P) := 
begin
 induction n,
 triv,
 apply and_of_map_aux_lower,
 apply and.left H
end

theorem forall_of_and_of_map : Π {n : ℕ} {P : fin n → Prop} (H : and_of_map P) (k : fin n), P k
| 0 P H (fin.mk val is_lt) := absurd is_lt (not_lt_zero _)
| 1 P H (fin.mk val is_lt) := 
  have H1 : val = 0, from eq_zero_of_lt_one is_lt, 
  begin revert is_lt, rw H1, intro, apply H  end
| (n+2) P H k :=
  begin 
   induction k, 
   cases (decidable.em (val < n+1)), 
   {apply @of_fin_prop_lower _ _ (fin.mk val is_lt) a,
   apply forall_of_and_of_map,
   apply and_of_map_lower,
   apply H},
   {assert veq : val = n+1,
   apply eq_of_ge_of_lt_succ,
   apply le_of_not_gt a,
   apply is_lt,
   revert is_lt,
   rw veq,
   intro,
   apply and.right H}
  end
