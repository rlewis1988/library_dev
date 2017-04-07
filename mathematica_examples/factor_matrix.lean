/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/

import init.meta.mathematica .bquant .datatypes .and_of_map ..data.rat .comp_val
open expr tactic rat

/-
For this example, we give a very brief development of matrices as lists of lists.
-/

@[reducible]
def {u} ith {α : Type u} [inhabited α] (l : list α) (i : ℕ) : α :=
match l^.nth i with
| some a := a
| none   := default α
end

/--
The transpose of a list-of-lists matrix
-/
def {u} transpose_list {α : Type u} [inhabited α] (m : list (list α)) : list (list α) :=
list.map (λ i, m^.map (λ l, ith l i)) (native.upto (ith m 0)^.length)

/--
The dot product of two list "vectors"
-/
def {u} dot_lists {α : Type u} [has_zero α] [has_mul α] [has_add α] : list α → list α → α
| [a] [b] := a*b
| (h1::t1) (h2::t2) := h1*h2 + dot_lists t1 t2
| _ _ := 0

/--
The product of two list-of-lists matrices
-/
def {u} mul_lists {α : Type u} [has_zero α] [has_mul α] [has_add α] [inhabited α]
       (m1 m2 : list (list α))  : list (list α) :=
list.map (λ i, (list.map (λ j, dot_lists (ith m1 i) (ith (transpose_list m2) j)) 
         (native.upto (ith m1 0)^.length))) (native.upto m1^.length)
   
infix `**`:50 := mul_lists

@[reducible]
def {u} is_lower_triangular {α : Type u} [has_lt α] [has_zero α] (m : list (list α)) : Prop :=
∀ i : fin (m^.length), ∀ j : fin ((ith m i^.val)^.length), i^.val < j^.val → ith (ith m i^.val) j^.val = 0

@[reducible]
def {u} is_upper_triangular {α : Type u} [has_lt α] [has_zero α] (m : list (list α)) : Prop :=
∀ i : fin (m^.length), ∀ j : fin ((ith m i^.val)^.length), i^.val > j^.val → ith (ith m i^.val) j^.val = 0





/-
On data types with decidable (in)equality, we can simplify the implementation using this tactic
to do arithmetic. However, it can be slow.
-/
meta def dec_triv_tac : tactic unit :=
do t ← target,
   to_expr `(dec_trivial : %%t) >>= apply

/--
Takes an expression of the form a < b, tries to find a proof that a ≥ b, and applies absurd.
-/
meta def dec_false (e : expr) : tactic unit :=
do md ← mk_mvar, md2 ← mk_mvar,
   tp ← infer_type e,
   (do to_expr `(%%md < %%md2) >>= unify tp,
   nmd ← ((do (v,_) ← instantiate_mvars md >>= norm_num,return v) <|> (make_expr_into_num md)), 
   nmd2 ← ((do (v,_) ← instantiate_mvars md2 >>= norm_num, return v) <|> (make_expr_into_num md2)), 
   ge ← to_expr `(%%nmd ≥ %%nmd2),
   gep ← mk_inhabitant_using ge gen_comp_val,
   to_expr `(absurd %%e (not_lt_of_ge %%gep)) >>= apply)

meta def unify_with_eq (e : expr) : tactic (expr × expr) :=
do e1 ← mk_mvar, e2 ← mk_mvar,
   to_expr `(%%e1 = %%e2) >>= unify e,
   return $ (e1, e2)

meta def triangularity_tac_aux : tactic unit :=
do t ← target, i ← mk_mvar, j ← mk_mvar, P ← mk_mvar, 
target >>= whnf >>= change,  
dsimp,
to_expr `(%%i < %%j → %%P) >>= unify t, 
 h ← mk_fresh_name >>= intro, 
(dec_false h  <|> do 
 (e1, e2) ← target >>= unify_with_eq, to_expr `(%%e1 = %%e2) >>= change, 
 reflexivity)

/--
Tries to automatically solve goals of the form is_(upper/lower)_triangluar m,
by transforming the quantifications to conjunctions and testing for 0s.
-/
meta def triangularity_tac : tactic unit := solve1 $
do dsimp, aom ← mk_mvar,
   refine `(forall_of_and_of_map %%aom),
   repeat (applyc `and.intro),
   all_goals $ solve1 $ 
     (do aom' ← mk_mvar, 
         refine `(forall_of_and_of_map %%aom'), 
         repeat (applyc `and.intro), 
         all_goals (triangularity_tac_aux))


meta def refine_lhs : expr → expr → (expr → expr → tactic expr) → tactic expr
| lhs ```(list.cons %%h %%t) f :=
  do v1 ← mk_mvar, v2 ← mk_mvar,
     to_expr `(%%v1 :: %%v2) >>= unify lhs,
     rc ← refine_lhs v2 t f,
     nh ← f v1 h,
     to_expr `(%%nh::%%rc)
| lhs ```(@list.nil %%t) _ := to_expr `(@list.nil %%t)
| _ _ _ := failed

/--
When rhs is a list of lists, refine_lhs_outer lhs rhs tries to unify
lhs to the same form as rhs. E.g., if rhs is [[1, 2], [3, 4]], will try to
match lhs to [[a, b], [c, d]].
-/
meta def refine_lhs_outer (lhs rhs : expr) : tactic expr :=
refine_lhs lhs rhs (λ e1 e2, refine_lhs e1 e2 (λ e3 e4, return e3))

/--
Proves that the product of two list-of-lists matrices is another list-of-lists matrix.
-/
meta def mk_mul_prf : tactic unit :=
do t ← target,
   lhs ← mk_mvar, rhs ← mk_mvar,
   to_expr `(%%lhs = %%rhs) >>= unify t,
   e ← whnf rhs >>= refine_lhs_outer lhs,
   to_expr `(%%e = %%rhs) >>= change,
   repeat 
     (do applyc `congr_helper,
     repeat 
       (do applyc `congr_helper,
       dsimp,
       t ← target,
       [_, lhs, rhs] ← return $ get_app_args t,
       lhs' ← make_expr_into_sum lhs,
       to_expr `(%%lhs' = %%rhs) >>= change,
       (_, prf) ← norm_num lhs',
       apply prf), 
     reflexivity),
   cleanup, reflexivity

/-
lu_tac looks for a target of the form 
∃ l u, is_lower_triangluar l ∧ is_upper_triangular u ∧ l**u = M
where M is a matrix, and proves this using Mathematica's LUDecomposition.
matrix_factor.m is an extra file that defines LUDecomp, a variant on LUDecomposition
that returns more appropriate data.

In general, the product l**u is only equal to M up to a row permutation.
This tactic does not handle that; it will only succeed if the permutation is the identity.
We leave it as an exercise for the reader to extend!
-/
meta def lu_tac : tactic unit := 
do t ← target, 
   (lam _ _ _ bd) ← return $ app_arg t,
   (lam _ _ _ ande) ← return $ app_arg bd,
   ```(%%_ ∧ %%_ ∧ %%_ = %%e) ← return $ ande,
   tp ← infer_type e,
   m ← mathematica.run_command_on_using
      (λ e, e ++ " // LeanForm // Activate // LUDecomp")
       e 
      "matrix_factor.m",
   m2 ← to_expr `((%%m : list %%tp)),
   lhs ← to_expr `(ith %%m2 0), rhs ← to_expr `(ith %%m2 1),
   existsi lhs, existsi rhs,
   split, triangularity_tac, split, triangularity_tac, mk_mul_prf


-- the examples below take a few seconds to run, and can bog down the editor.
-- remove the #exit command to try them.
#exit
example : ∃ l u, is_lower_triangular l ∧ is_upper_triangular u ∧ l ** u = [[(1 : ℤ), 2], [3, 4]] := 
by lu_tac

example : ∃ l u, is_lower_triangular l ∧ is_upper_triangular u
             ∧ l ** u = [[(1 : ℤ), 2, 3], [1, 4, 9], [1, 8, 27]] := 
by lu_tac

example : ∃ l u, is_lower_triangular l ∧ is_upper_triangular u
             ∧ l ** u = [[(1 : ℝ), 2, 3, 4, 5],  [0, -1, 3, -5, 8], [1, 4, 9, 10, 20], [1, -1, 0, -10, 5], [1, 8, 27, -11, 0]] := 
by lu_tac
