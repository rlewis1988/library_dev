/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/

import ..data.list.basic .matrix ..algebra.order ..data.fin ..data.int.basic init.meta.mathematica init.meta.smt.smt_tactic .and_of_map ..mathematica_examples.comp_val
open expr tactic rb_map

def linarith_path := "~/lean/lean/extras/mathematica/linarith.m"
--"c:/msys64/home/robyl/lean/lean/extras/mathematica/linarith.m"

private meta def find_vars_aux2 : expr → rb_map expr unit
| (app (app (app (app (const ``add _) _) _) u) v) := union (find_vars_aux2 u) (find_vars_aux2 v)
| (app (app (app (app (const ``mul _) _) _) u) v) :=
  if (is_signed_num u) then insert (mk _ _) v unit.star else mk _ _
| _ := mk _ _

private meta def find_vars (l : list expr) : rb_map expr unit :=
list.foldr (λ e m, union m (find_vars_aux2 e)) (mk _ _) l

private meta def mk_var_map : expr → rb_map expr expr
| (app (app (app (app (const ``add _) _) _) u) v) := union (mk_var_map u) (mk_var_map v)
| (app (app (app (app (const ``mul _) _) _) u) v) :=
  if (is_signed_num u) then insert (mk _ _) v u else mk _ _
| _ := mk _ _

private meta def sum_eq_aux (m : rb_map expr expr) (e z : expr) : expr :=
match (find m e) with
| (some d) := d
| none   := z
end

private meta def sum_with_zeros_aux (e z : expr) : list expr → tactic expr
| []       := return z
| [h]      :=
  let var_to_coeff := mk_var_map e, coeff := sum_eq_aux var_to_coeff h z in
  mk_app `mul [coeff, h]
| (h :: t) :=
  let var_to_coeff := mk_var_map e, coeff := sum_eq_aux var_to_coeff h z in 
  do prod ← mk_app `mul [coeff, h],
     sum ← sum_with_zeros_aux t,
     mk_app `add [prod, sum]

private meta def sum_with_zeros (e : expr) (l : list expr) : tactic expr := 
do etp ← infer_type e,
   ez ← to_expr `((0 : %%etp)),
   sum_with_zeros_aux e ez l

/--
  e is a sum (a*x + b*y + ...)
  l is a list of variables that includes all variables in e
  returns a proof that e is equal to the sum over l, with 0 coeffs inserted where needed
-/
meta def sum_eq_sum_with_zeros (e : expr) (l : list expr) : tactic (expr × expr) := do
 sum ← sum_with_zeros e l,
 eqp ← to_expr `(%%e = %%sum),
 eqpr ← mk_inhabitant_using eqp simp,
 return (sum, eqpr)

attribute [simp] zero_mul add_zero add_assoc 

private meta def coeff_matrix_aux (e z : expr) (vars : list expr) : list expr :=
let mv := mk_var_map e in
 list.map (λ v, match (find mv v) with
 | some d := d
 | none   := z
 end) vars

meta def coeff_matrix (l : list expr) (vars : list expr) : tactic (list (list expr)) :=
 match l with
 | [] := failed
 | (h :: t) := 
   do tp ← infer_type h,
      zr ← to_expr `((0 : %%tp)),
      return $ l^.map (λ e, coeff_matrix_aux e zr vars)
 end

def bool_filter {α : Type} (P : α → bool) : list α → list α
| []       := []
| (h :: t) := if P h then h :: bool_filter t else bool_filter t


private meta def sep_lin_hyp (e : expr) : expr × expr :=
match get_app_args e with
| [_, _, a, b] := (a, b)
| _            := (var 0, var 0)
end

private meta def sep_lin_hyp_with_rel (e : expr) : expr × expr × expr :=
match get_app_args e with
| [_, _, a, b] := (app_fn e, a, b)
| _            := (app_fn e, var 0, var 0)
end

private meta def sep_lin_hyps : list expr → list expr × list expr
| [] := ([], [])
| (h :: t) := 
  match (sep_lin_hyp h, sep_lin_hyps t) with
  | ((e1, e2), (l1, l2)) := (e1::l1, e2::l2)
  end

private meta def find_vars_in_comps (l : list expr) : rb_map expr unit :=
let (lhss, rhss) := sep_lin_hyps l in
union (find_vars lhss) (find_vars rhss)

-- takes a list of comparison expressions, all with the same comparison
-- returns a pair of a matrix and a vector: eg A, b st A x ≤ b
meta def create_farkas_matrix (l : list expr) (vars : list expr) : tactic (list (list expr) × list expr) :=
match sep_lin_hyps l with
| (sums, vals) := 
  do cf ← coeff_matrix sums vars,
  return (cf, vals)
end


open list

def vec_prod {A : Type} [semiring A] : list A → list A → A
| [] [] := 0
| (h1 :: t1) (h2 :: t2) := h1 * h2 + vec_prod t1 t2
| _ _ := 0

def mat_prod {A : Type} [semiring A] (mat : list (list A)) (vec : list A) : list A :=
mat^.map (λ row, vec_prod row vec)

lemma subst_helper {A : Type} {m n o : A} {R : A → A → Prop} (H1 : m = n) (H2 : R m o) : R n o :=
eq.subst H1 H2

meta def flatten_expr_list : list expr → tactic expr
| [] := failed
| [h] := to_expr `([ %%h ])
| (h :: t) := do fl ← flatten_expr_list t, mk_app ``list.cons [h, fl]

meta def flatten_matrix : list (list expr) → tactic expr
| [] := failed
| [h] := do fh ← flatten_expr_list h, to_expr `([%%fh])
| (h :: t) := do fh ← flatten_expr_list h, ft ← flatten_matrix t, mk_app ``list.cons [fh, ft]


-- takes a comparison e of form t R c, and a list of vars l.
-- produces a proof that vec_prod (coeff_matrix_aux e l) l R c
meta def expand_ineq_proof (e : expr) (l : list expr) : tactic expr :=
do etp ← infer_type e,
match sep_lin_hyp_with_rel etp with
| (R, t, c) := 
  do tp ← infer_type t,
     zr ← to_expr `((0 : %%tp)),
     coeffs ← flatten_expr_list $ coeff_matrix_aux t zr l,
     vars ← flatten_expr_list l,
     vpr ← mk_app `vec_prod [coeffs, vars],
     sumpr ← sum_eq_sum_with_zeros t l,
     match sumpr with
     | (_, prf) := do pt ← infer_type prf, et ← infer_type e,  mk_app ``subst_helper [prf, e]
     end
end

meta def fold_intros : expr → list expr → tactic expr
| dft [] := return dft
| _ [h] := return h
| _ [h1, h2] := to_expr `(and.intro %%h1 %%h2)
| dft (h1 :: h2 :: t) := do l ← to_expr `(and.intro %%h1 %%h2), fold_intros dft (l :: t)


meta def not_exists_of_linear_hyps (hyps : list name) : tactic unit := do
 lhyps ← monad.mapm get_local hyps,
 hyptps ← monad.mapm infer_type lhyps,
 [tp, _, _, _] ← return $ get_app_args (head hyptps),
 let vars := keys (find_vars_in_comps hyptps),
 expanded_proofs ← monad.mapm (λ e, expand_ineq_proof e vars) lhyps,
 expanded_tps ← monad.mapm infer_type expanded_proofs,
 varl ← flatten_expr_list vars,
 (mat, vec) ← create_farkas_matrix hyptps vars,
 mat' ← flatten_matrix mat, vec' ← flatten_expr_list vec,
 fin_form_mat ← to_expr `(matrix_of_list_of_lists %%mat' (length %%mat') (length %%varl)),
 varvec ← to_expr `(cvector_of_list %%varl),
 rhsvec ← to_expr `(cvector_of_list %%vec'),
 hyptps' ← flatten_expr_list hyptps,
 witnessp ← mathematica.run_command_on_using (λ s, s ++ " // LeanForm // Activate // FindFalseCoeffs")
                                     hyptps' linarith_path,
 witness ← to_expr `(rvector_of_list (%%witnessp : list %%tp)),
 trace witness,
 zd ← to_expr `((dec_trivial : ∀ i, r_ith (%%witness ⬝ %%fin_form_mat) i = 0)), 
 trace zd,
 /-comp_lhs ← to_expr `(c_dot ((%%witness)^Tr) %%rhsvec) >>= make_expr_into_sum,
 comp0 ← to_expr `(%%comp_lhs < 0),
 trace comp0,
 zor ← mk_inhabitant_using comp0 gen_comp_val,-/
 to_expr `(c_dot ((%%witness)^Tr) %%rhsvec) >>= infer_type >>= trace,
 zor ← to_expr `(dec_trivial : c_dot ((%%witness)^Tr) %%rhsvec < (0 : %%tp)),
 nex ← to_expr `(motzkin_transposition_le %%fin_form_mat %%rhsvec %%witness %%zd %%zor),
 apply nex,
 existsi varvec,
 conjpr ← fold_intros ```(trivial) expanded_proofs,
 apply conjpr

/-
returns (list of lt proof terms, list of lt types, list of le proof terms, list of le types, list of eq proof terms, list of eq types)
-/
private meta def split_lin_hyps : list expr → tactic (list expr × list expr × list expr × list expr × list expr × list expr)
| [] := return ([], [], [], [], [], [])
| (h::t) := 
  do tp ← infer_type h,
     (lt, ltts, le, lets, eq, eqts) ← split_lin_hyps t,
     if is_app_of tp `lt then return (h::lt, tp::ltts, le, lets, eq, eqts) else
     if is_app_of tp `le then return (lt, ltts, h::le, tp::ltts, eq, eqts) else
     if is_app_of tp `eq then return (lt, ltts, le, lets, h::eq, tp::eqts) else
     failed

meta def create_flattened_farkas_pair (l vars : list expr) : tactic (expr × expr) :=
do (mat, vec) ← create_farkas_matrix l vars,
   mat' ← flatten_matrix mat, vec' ← flatten_expr_list vec,
   return (mat', vec')

meta def mk_fin_form_mat (vars mat : expr) : tactic expr :=
to_expr `(matrix_of_list_of_lists %%mat (length %%mat) (length %%vars))

meta def mk_fin_form_vec (vec : expr) : tactic expr :=
to_expr `(cvector_of_list %%vec)

meta def not_exists_of_linear_hyps_gen (hyps : list name) : tactic unit := do
 (ltpfs, lttps, lepfs, letps, eqpfs, eqtps) ← monad.mapm get_local hyps >>= split_lin_hyps,
-- lhyps ← monad.mapm get_local hyps,
-- hyptps ← monad.mapm infer_type lhyps,
 let hyptps := append (append lttps letps) eqtps,
 (tp::_) ← get_app_args $ kth hyptps 0,
 let vars := keys $ find_vars_in_comps hyptps,
 [expltpfs, explepfs, expeqpfs] ← monad.mapm 
   (λ l, monad.mapm (λ e, expand_ineq_proof e vars) l) 
   [ltpfs, lepfs, eqpfs],
-- expanded_proofs ← monad.mapm (λ e, expand_ineq_proof e vars) lhyps,
 varl ← flatten_expr_list vars,
 [(ltmat, ltvec), (lemat, levec), (eqmat, eqvec)] ← monad.mapm (λ l, create_flattened_farkas_pair l vars) [lttps, letps, eqtps],
-- (mat, vec) ← create_farkas_matrix hyptps vars,
-- mat' ← flatten_matrix mat, vec' ← flatten_expr_list vec,
 [finltmat, finlemat, fineqmat] ← monad.mapm (mk_fin_form_mat varl) [ltmat, lemat, eqmat],
-- fin_form_mat ← to_expr `(matrix_of_list_of_lists %%mat' (length %%mat') (length %%varl)),
 varvec ← to_expr `(cvector_of_list %%varl),
 [finltvec, finlevec, fineqvec] ← monad.mapm mk_fin_form_vec [ltvec, levec, eqvec],
-- rhsvec ← to_expr `(cvector_of_list %%vec'),
 [flttps, fletps, feqtps] ← monad.mapm flatten_expr_list [lttps, letps, eqtps],
-- hyptps' ← flatten_expr_list hyptps,
 witnessp ← mathematica.run_command_on_list_using (λ s, "Module[{hl:="++s++"}, With[{lts=hl[[1]] // LeanForm // Activate, les=hl[[2]] // LeanForm // Activate, eqs=hl[[3]] // LeanForm // Activate}, FindFalseCoeffs[lts, les, eqs]]]")
                                     (append (append flttps fletps) feqtps) linarith_path,
 witness_list ← to_expr `(%%witnessp : list (list int)),
 [ltv, lev, eqv] ← eval_expr (list (list int)) witness_list,
 witness ← to_expr `(rvector_of_list (%%witnessp : list int)),
 zd ← to_expr `((dec_trivial : ∀ i, r_ith (%%witness ⬝ %%fin_form_mat) i = 0)), 
 comp_lhs ← to_expr `(c_dot ((%%witness)^Tr) %%rhsvec) >>= make_expr_into_sum,
 comp0 ← to_expr `(%%comp_lhs < 0),
 zor ← mk_inhabitant_using comp0 gen_comp_val,
 nex ← to_expr `(motzkin_transposition_le %%fin_form_mat %%rhsvec %%witness %%zd %%zor),
 apply nex,
 existsi varvec,
 conjpr ← fold_intros ```(trivial) expanded_proofs,
 apply conjpr

namespace tactic
namespace interactive
section
open lean.parser interactive.types interactive

meta def not_exists_of_linear_hyps (ids : parse (many ident)) : tactic unit :=
_root_.not_exists_of_linear_hyps ids


end
end interactive
end tactic


-- matrix manipulations
open matrix nat

def matrix_of_list_of_lists {A : Type} [inhabited A] (l : list (list A)) (m n : ℕ) :
  matrix A m n :=
λ i j, if Hil : ↑i < length l then
 let r := ith l i Hil in
  if Hjr : ↑j < length r then ith r j Hjr
  else default A
 else default A


def vec_le {A : Type} [order_pair A] {n : ℕ} (v1 v2 : rvector A n) := ∀ i : fin n, r_ith v1 i ≤ r_ith v2 i


section farkas

variables {A : Type} [linear_ordered_ring A] {a b c n : ℕ}
        (P : M[A]_(a, n)) (Q : M[A]_(b, n)) (R : M[A]_(c, n))
        (p : cvector A a) (q : cvector A b) (r : cvector A c)
        (y : rvector A a) (z : rvector A b) (t : rvector A c)
        (Hsum : ∀ i : fin n, r_ith (y ⬝ P) i + r_ith (z ⬝ Q) i + r_ith (t ⬝ R) i = 0)

include Hsum
theorem motzkin_transposition_with_equalities_conj
        (Hor : (c_dot (y^Tr) p + c_dot (z^Tr) q + c_dot (t^Tr) r < 0) ∨
               ((∃ i : fin a, r_ith y i > 0) ∧ c_dot (y^Tr) p + c_dot (z^Tr) q + c_dot (t^Tr) r ≤ 0)) :
         ¬ ∃ x : cvector A n, and_of_map (λ i, c_ith (P ⬝ x) i < c_ith p i)
                           ∧  and_of_map (λ i, c_ith (Q ⬝ x) i ≤ c_ith q i)
                           ∧  and_of_map (λ i, c_ith (R ⬝ x) i = c_ith r i) :=
assume ⟨x, ⟨Hx1, Hx2, Hx3⟩⟩,
let Hx1' := forall_of_and_of_map Hx1 in
let Hx2' := forall_of_and_of_map Hx2 in
let Hx3' := forall_of_and_of_map Hx3 in
absurd (exists.intro x (and.intro Hx1' (and.intro Hx2' Hx3')))
 (begin
   apply motzkin_transposition_with_equalities,
   repeat {assumption}
  end)

omit Hsum

def zero_mat {n : ℕ} {A : Type} : M[A]_(0, n) := λ k l, absurd (fin.is_lt k) (not_lt_zero _)
def mat_zero {m : ℕ} {A : Type} : M[A]_(m, 0) := λ k l, absurd (fin.is_lt l) (not_lt_zero _)
theorem motzkin_transposition_le (Hsum' : ∀ i : fin n, r_ith (z ⬝ Q) i = 0)
(Hor : c_dot (z^Tr) q < 0)
: ¬ ∃ x : cvector A n, and_of_map  (λ i, c_ith (Q ⬝ x) i ≤ c_ith q i) :=
have H1 :  (∀ (i : fin n), r_ith (mat_zero⬝zero_mat) i + r_ith (z⬝Q) i + r_ith (mat_zero⬝zero_mat) i = 0),
begin
 intro i,
 change 0 + (z⬝Q) (fin.zero 0) i  + 0 = 0,
 simp, apply Hsum'
end,
/-have H2 : c_dot (mat_zero^Tr) zero_mat + c_dot (z^Tr) q + c_dot (mat_zero^Tr) zero_mat < 0 ∨ (∃
 (i : fin 0), r_ith (mat_zero) i > 0) ∧ c_dot (mat_zero^Tr) zero_mat + c_dot (z^Tr) q + c_dot (mat_zero^Tr) zero_mat ≤ 0,
begin
 left,
 change 0 + c_dot (z^Tr) q + 0 < 0,
 simp, assumption
end,-/
let mtleaux := motzkin_transposition_with_equalities_conj
                   zero_mat Q zero_mat zero_mat q zero_mat mat_zero z mat_zero H1
    begin left, change 0 + c_dot (z^Tr) q + 0 < 0, simp, assumption end -- why won't this unify with H2?
in
begin
 intro HEX,
 apply mtleaux,
 cases HEX with x HEx,
 existsi x,
 constructor,
 apply trivial,
 constructor,
 assumption,
 apply trivial
end

end farkas
