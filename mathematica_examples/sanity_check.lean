/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/

import init.meta.mathematica init.meta.rb_map .datatypes
open expr tactic rb_set tactic.mathematica

/--
find_locals e returns a set containing all local variables in e.
-/
meta def find_locals : expr → expr_set :=
λ e, e^.fold (mk_expr_set) (λ e' _ l, if is_local_constant e' then l^.insert e' else l)


/--
sanity_check_aux hs xs takes a list of exprs hs, and a list of exprs xs, 
which are local variables that can appear in the exprs in hs.
It fails if it finds an instantiation for the xs that makes all hs true.
-/
meta def sanity_check_aux (hs : list expr) (xs : list expr) : tactic unit :=
do hs' ← monad.foldl (λ a b, to_expr `(%%a ∧ %%b)) ```(true) hs,
   l ← run_command_on_list 
      (λ e, "With[{ls=Map[Activate[LeanForm[#]]&,"++e++"]}, Length[FindInstance[ls[[1]], Drop[ls, 1]]]]") 
      (hs'::xs),
   n ← to_expr `(%%l : ℕ) >>= eval_expr ℕ, 
   if n > 0 then 
      fail "sanity check: the negation of the goal is consistent with hypotheses" 
   else skip

/--
sanity_check collects the local hypotheses, identifies the local variables
in them and in the goal, and fails if it finds an instantiation for these
variables that makes the hypotheses true and the goal false.
-/
meta def sanity_check : tactic unit :=
do hyps ← local_context, 
   phyp ← monad.filter is_proof hyps,
   hypt ← monad.mapm infer_type phyp, 
   t ← target,
   vars ← return $ rb_map.keys $ list.foldr (λ e s, rb_map.union s (find_locals e)) mk_expr_set (t::hypt),
   nt ← to_expr `(¬ %%t),
   sanity_check_aux (nt::hypt) vars
   
/-
EXAMPLES.

Note: the "admit" tactic is a proof by sorry.
-/

-- this example succeeds, since the goal is plausible.
example (x : ℤ) (h : x < 0) : x < 0 :=
by sanity_check; admit

-- this example fails, since the goal does not necessarily hold.
example (x : ℝ) (h1 : sin x = 0) (h2 : cos x > 0) : x = 0 :=
by sanity_check; admit

-- adding an additional hypothesis to the previous example lets it succeed.
example (x : ℝ) (h1 : sin x = 0) (h2 : cos x > 0) (h3 : -pi < x ∧ x < pi)
 : x = 0 :=
by sanity_check; admit
