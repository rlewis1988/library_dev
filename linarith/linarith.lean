/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/

import ..data.list.basic .matrix ..algebra.order .comp_val ..data.fin ..data.int.basic init.meta.mathematica ..tools.auto.mk_inhabitant init.meta.smt.smt_tactic .and_of_map
open expr tactic rb_map

def linarith_path := "~/lean/lean/extras/mathematica/linarith.m"
--"c:/msys64/home/robyl/lean/lean/extras/mathematica/linarith.m"

meta def find_vars_aux2 : expr → rb_map expr unit
| (app (app (app (app (const ``add _) _) _) u) v) := union (find_vars_aux2 u) (find_vars_aux2 v)
| (app (app (app (app (const ``mul _) _) _) u) v) :=
  if (is_signed_num u) then insert (mk _ _) v unit.star else mk _ _
| _ := mk _ _

meta def find_vars (l : list expr) : rb_map expr unit :=
list.foldr (λ e m, union m (find_vars_aux2 e)) (mk _ _) l

meta def mk_var_map : expr → rb_map expr expr
| (app (app (app (app (const ``add _) _) _) u) v) := union (mk_var_map u) (mk_var_map v)
| (app (app (app (app (const ``mul _) _) _) u) v) :=
  if (is_signed_num u) then insert (mk _ _) v u else mk _ _
| _ := mk _ _

meta def sum_eq_aux (m : rb_map expr expr) (e z : expr) : expr :=
match (find m e) with
| (some d) := d
| none   := z
end

meta def sum_with_zeros_aux (e z : expr) : list expr → tactic expr
| []       := return z
| [h]      :=
  let var_to_coeff := mk_var_map e, coeff := sum_eq_aux var_to_coeff h z in
  mk_app `mul [coeff, h]
| (h :: t) :=
  let var_to_coeff := mk_var_map e, coeff := sum_eq_aux var_to_coeff h z in 
  do prod ← mk_app `mul [coeff, h],
     sum ← sum_with_zeros_aux t,
     mk_app `add [prod, sum]

meta def sum_with_zeros (e : expr) (l : list expr) : tactic expr := 
do etp ← infer_type e,
   ez ← to_expr `((0 : %%etp)),
   sum_with_zeros_aux e ez l
#check lt_succ_of_lt
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

attribute [simp] zero_mul add_zero add_assoc --mul_comm

meta def coeff_matrix_aux (e z : expr) (vars : list expr) : list expr :=
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

-- split a list of linear hypotheses into strict <, weak ≤, and eq =
meta def split_lin_hyps (l : list expr) : list expr × list expr × list expr :=
⟨bool_filter (λ e, is_app_of e `lt) l, bool_filter (λ e, is_app_of e `le) l, bool_filter (λ e, is_app_of e `eq) l⟩

meta def sep_lin_hyp (e : expr) : expr × expr :=
match get_app_args e with
| [_, _, a, b] := (a, b)
| _            := (var 0, var 0)
end

meta def sep_lin_hyp_with_rel (e : expr) : expr × expr × expr :=
match get_app_args e with
| [_, _, a, b] := (app_fn e, a, b)
| _            := (app_fn e, var 0, var 0)
end

meta def sep_lin_hyps : list expr → list expr × list expr
| [] := ([], [])
| (h :: t) := 
  match (sep_lin_hyp h, sep_lin_hyps t) with
  | ((e1, e2), (l1, l2)) := (e1::l1, e2::l2)
  end

meta def find_vars_in_comps (l : list expr) : rb_map expr unit :=
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


meta def make_mat_eq_prf : tactic unit := do
 dunfold [`r_ith, `rvector_of_list, `matrix_of_list_of_lists, `mul, `r_ith],
 dsimp,
 (lhs, rhs) ← target >>= match_eq,
 (lhsv, lhsp) ← norm_num lhs,
 (rhsv, rhsp) ← norm_num rhs,
 to_expr `(eq.trans %%lhsp (eq.symm %%rhsp)) >>= apply

meta def make_and (e : expr) : tactic expr :=
do m1 ← mk_mvar, m2 ← mk_mvar, m3 ← mk_mvar, m4 ← mk_mvar,
   to_expr `(@eq %%m3 %%m1 (@zero %%m3 %%m4) ∧ %%m2) >>= unify e,
   to_expr `(%%m1 = 0 ∧ %%m2)

meta def prove_and : tactic unit :=
do i ← mk_const `and.intro, apply_core i {md:=transparency.all, approx:=tt},
 applyc `eq.refl

meta def not_exists_of_linear_hyps (hyps : list name) : tactic unit := do
 lhyps ← monad.mapm get_local hyps,
 hyptps ← monad.mapm infer_type lhyps,
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
 witness ← to_expr `(rvector_of_list (%%witnessp : list int)),
 fas ← to_expr `(∀ i, r_ith (%%witness ⬝ %%fin_form_mat) i = 0),
-- zd ← mk_inhabitant_using fas (applyc `forall_of_and_of_map >> tactic.repeat prove_and >> applyc `eq.refl),
/- zd ← mk_inhabitant_using fas 
 ( applyc `forall_of_and_of_map >> tactic.repeat (do
     trace "tgt", trace_state, an ← target >>= make_and, trace "an", change an,
     applyc `and.intro, dsimp >> trace "ZERO" >> reflexivity >> trace "ONE") >> dsimp >> reflexivity),-/
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
