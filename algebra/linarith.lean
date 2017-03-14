import ..data.list.basic .matrix .order ..data.fin ..data.int.basic init.meta.mathematica
open expr tactic nat rb_map

def linarith_path := "~/lean/lean/extras/mathematica/linarith.m"
--"c:/msys64/home/robyl/lean/lean/extras/mathematica/linarith.m"

meta def rb_map_union  {key : Type} {data : Type} (m1 m2 : rb_map key data) : rb_map key data :=
fold m1 m2 (λ k d m, insert m k d)

meta def is_num : expr → bool := λ t, tt


--meta def is_num : expr → bool := λ t, --tt
--is_app_of t `zero || is_app_of t `one || is_app_of t `bit0 || is_app_of t `bit1

meta def find_vars_aux2 : expr → rb_map expr unit
| (app (app (app (app (const ``add _) _) _) u) v) := rb_map_union (find_vars_aux2 u) (find_vars_aux2 v)
| (app (app (app (app (const ``mul _) _) _) u) v) :=
  if (is_num u) then insert (mk _ _) v unit.star else mk _ _
| _ := mk _ _

meta def find_vars (l : list expr) : rb_map expr unit :=
list.foldr (λ e m, rb_map_union m (find_vars_aux2 e)) (mk _ _) l

-- the order of the resulting list isn't deterministic

meta def mk_var_map : expr → rb_map expr expr
| (app (app (app (app (const ``add _) _) _) u) v) := rb_map_union (mk_var_map u) (mk_var_map v)
| (app (app (app (app (const ``mul _) _) _) u) v) :=
  if (is_num u) then insert (mk _ _) v u else mk _ _
| _ := mk _ _

meta def sum_eq_aux (m : rb_map expr expr) (e z : expr) : expr :=
match (find m e) with
| (some d) := d
| none   := z
end

meta def sum_with_zeros_aux (e z : expr) : list expr → tactic expr
| []       := return z
| [h]      :=
 let var_to_coeff := mk_var_map e, coeff := sum_eq_aux var_to_coeff h z in do
 mk_app `mul [coeff, h]
| (h :: t) :=
 let var_to_coeff := mk_var_map e, coeff := sum_eq_aux var_to_coeff h z in do
 prod ← mk_app `mul [coeff, h],
 sum ← sum_with_zeros_aux t,
 mk_app `add [prod, sum]

meta def sum_with_zeros (e : expr) (l : list expr) : tactic expr := do
 etp ← infer_type e,
 ez ← to_expr `((0 : %%etp)),
 sum_with_zeros_aux e ez l


-- e is a sum, l is a list of variables that includes all the ones in e.
-- returns a proof that e is equal to the sum over l with the right coeffs
meta def sum_eq_sum_with_zeros (e : expr) (l : list expr) : tactic (expr × expr) := do
 sum ← sum_with_zeros e l,
 lms ← simp_lemmas.mk_default,
 esimpe ← simplify_core {} lms `eq e,
 ssimpe ← simplify_core {} lms `eq sum,
 match (esimpe, ssimpe) with
 | ((esimped, esimpedpr), (ssimped, ssimpedpr)) := do
   eqpr1 ← mk_app `eq.symm [ssimpedpr],
   eqpr ← mk_app `eq.trans [esimpedpr, eqpr1],
   return (sum, eqpr)
 end

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
 | (h :: t) := do
  tp ← infer_type h,
  zr ← to_expr `((0 : %%tp)),
 return (list.map (λ e, coeff_matrix_aux e zr vars) l)
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
| (h :: t) := match (sep_lin_hyp h, sep_lin_hyps t) with
 | ((e1, e2), (l1, l2)) := (e1::l1, e2::l2)
end

meta def find_vars_in_comps (l : list expr) : rb_map expr unit :=
let (lhss, rhss) := sep_lin_hyps l in
rb_map_union (find_vars lhss) (find_vars rhss)

-- takes a list of comparison expressions, all with the same comparison
-- returns a pair of a matrix and a vector: eg A, b st A x ≤ b
meta def create_farkas_matrix (l : list expr) (vars : list expr) : tactic (list (list expr) × list expr) :=
match sep_lin_hyps l with
| (sums, vals) := do
 cf ← coeff_matrix sums vars,
 return (cf, vals)
end


open list

def vec_prod {A : Type} [semiring A] : list A → list A → A
| [] [] := 0
| (h1 :: t1) (h2 :: t2) := h1 * h2 + vec_prod t1 t2
| _ _ := 0

def mat_prod {A : Type} [semiring A] (mat : list (list A)) (vec : list A) : list A :=
list.map (λ row, vec_prod row vec) mat

lemma subst_helper {A : Type} {m n o : A} {R : A → A → Prop} (H1 : m = n) (H2 : R m o) : R n o :=
eq.subst H1 H2

meta def flatten_expr_list : list expr → tactic expr
| [] := do trace "blah", failed
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
| (R, t, c) := do
  tp ← infer_type t,
  zr ← to_expr `((0 : %%tp)),
  coeffs ← flatten_expr_list $ coeff_matrix_aux t zr l,
  vars ← flatten_expr_list l,
  vpr ← mk_app `vec_prod [coeffs, vars],
  sumpr ← sum_eq_sum_with_zeros t l,
  match sumpr with
  | (_, prf) := do pt ← infer_type prf, et ← infer_type e,  mk_app ``subst_helper [prf, e]
  end
end

meta def tactic_map {α β : Type} (f : α → tactic β) : (list α) → tactic (list β)
| [] := return []
| (h :: t) := do fh ← f h, ft ← tactic_map t, return (fh :: ft)



meta def fold_intros : expr → list expr → tactic expr
| dft [] := return dft
| _ [h] := return h
| _ [h1, h2] := to_expr `(and.intro %%h1 %%h2)
| dft (h1 :: h2 :: t) := do l ← to_expr `(and.intro %%h1 %%h2), fold_intros dft (l :: t)


meta def make_mat_eq_prf : tactic unit := do
 dunfold [`r_ith, `rvector_of_list, `matrix_of_list_of_lists, `mul, `r_ith],
 dsimp,
 trace_state,
 (lhs, rhs) ← target >>= match_eq,
 (lhsv, lhsp) ← norm_num lhs,
 (rhsv, rhsp) ← norm_num rhs,
 to_expr `(eq.trans %%lhsp (eq.symm %%rhsp)) >>= apply


lemma foo (P : fin 2 → Prop) : P ⟨0, dec_trivial⟩ → P ⟨1, dec_trivial⟩ → ∀ i : fin 2, P i := sorry

/-
meta def not_exists_of_linear_hyps (hyps : list name) : tactic unit := do
 lhyps ← tactic_map get_local hyps,
 hyptps ← tactic_map infer_type lhyps,
 let vars := keys (find_vars_in_comps hyptps) in do
 expanded_proofs ← tactic_map (λ e, expand_ineq_proof e vars) lhyps,
 expanded_tps ← tactic_map infer_type expanded_proofs,
 varl ← flatten_expr_list vars,
 (mat, vec) ← create_farkas_matrix hyptps vars,
 mat' ← flatten_matrix mat, vec' ← flatten_expr_list vec,
 fin_form_mat ← to_expr `(matrix_of_list_of_lists %%mat' (length %%mat') (length %%varl)),
 varvec ← to_expr `(cvector_of_list %%varl),
 rhsvec ← to_expr `(cvector_of_list %%vec'),
 hyptps' ← flatten_expr_list hyptps,
 witnessp ← run_mm_command_on_expr_using (λ s, s ++ " // LeanForm // Activate // FindFalseCoeffs")
                                     hyptps' linarith_path,
 witness ← to_expr `(rvector_of_list (%%witnessp : list int)),
 zd ← to_expr `((dec_trivial : ∀ i, r_ith (%%witness ⬝ %%fin_form_mat) i = 0)),
 zor ← to_expr `((dec_trivial : c_dot ((%%witness)^Tr) %%rhsvec < 0)),
 nex ← to_expr `(motzkin_transposition_le %%fin_form_mat %%rhsvec %%witness %%zd %%zor),
 apply nex,
 existsi varvec,
 dp ← to_expr `(%%fin_form_mat ⬝ %%varvec),
 pred ← to_expr `(λ i, c_ith %%dp i ≤ c_ith %%rhsvec i),
 conj ← to_expr `(and_of_map %%pred),
 trv ← to_expr `(trivial),
 conjpr ← fold_intros trv expanded_proofs,
 apply conjpr
-/

meta def not_exists_of_linear_hyps (hyps : list name) : tactic unit := do
 lhyps ← tactic_map get_local hyps,
 hyptps ← tactic_map infer_type lhyps,
 let vars := keys (find_vars_in_comps hyptps) in do
 expanded_proofs ← tactic_map (λ e, expand_ineq_proof e vars) lhyps,
 expanded_tps ← tactic_map infer_type expanded_proofs,
 varl ← flatten_expr_list vars,
 (mat, vec) ← create_farkas_matrix hyptps vars,
 mat' ← flatten_matrix mat, vec' ← flatten_expr_list vec,
 fin_form_mat ← to_expr `(matrix_of_list_of_lists %%mat' (length %%mat') (length %%varl)),
 varvec ← to_expr `(cvector_of_list %%varl),
 rhsvec ← to_expr `(cvector_of_list %%vec'),
 hyptps' ← flatten_expr_list hyptps,
 witnessp ← run_mm_command_on_expr_using (λ s, s ++ " // LeanForm // Activate // FindFalseCoeffs")
                                     hyptps' linarith_path,
 witness ← to_expr `(rvector_of_list (%%witnessp : list int)),
 to_expr  `(∀ i, r_ith (%%witness ⬝ %%fin_form_mat) i = 0) >>= assert `zd,
 applyc `foo,
 repeat make_mat_eq_prf,
 trace "here",
-- trace_state,
 zor ← to_expr `((dec_trivial : c_dot ((%%witness)^Tr) %%rhsvec < 0)),
 nex ← to_expr `(motzkin_transposition_le %%fin_form_mat %%rhsvec %%witness zd %%zor),
 apply nex,
 existsi varvec,
 dp ← to_expr `(%%fin_form_mat ⬝ %%varvec),
 pred ← to_expr `(λ i, c_ith %%dp i ≤ c_ith %%rhsvec i),
 conj ← to_expr `(and_of_map %%pred),
 trv ← to_expr `(trivial),
 conjpr ← fold_intros trv expanded_proofs,
 apply conjpr


 


-- matrix manipulations
open matrix

def matrix_of_list_of_lists {A : Type} [inhabited A] (l : list (list A)) (m n : ℕ) :
  matrix A m n :=
λ i j, if Hil : ↑i < length l then
 let r := ith l i Hil in
  if Hjr : ↑j < length r then ith r j Hjr
  else default A
 else default A

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

lemma eq_of_ge_of_lt_succ {n k : ℕ} (h1 : k ≥ n) (h2 : k < n+1) : k = n := sorry
lemma eq_zero_of_lt_one {n : ℕ} (Hn : n < 1) : n = 0 := sorry

theorem reduce_fin {n : ℕ} (k : fin (succ n)) : k^.val = n ∨ ∃ k' : fin n, k = raise_fin k' :=
if H : k^.val ≥ n then or.inl (eq_of_ge_of_lt_succ H (fin.is_lt _)) else
or.inr (exists.intro (fin.mk k^.val (lt_of_not_ge H)) (begin induction k, reflexivity end))

/-theorem forall_of_and_of_map' : Π {n : ℕ} {P : fin n → Prop} (H : and_of_map P) (k : fin n), P k
| 0 P H (fin.mk val is_lt) := absurd (is_lt) (not_lt_zero _)
| (m+1) P H (fin.mk 0 is_lt) := begin induction m, {apply H}, {  } end
| (m+1) P H (fin.mk (k+1) is_lt) := sorry-/

theorem forall_of_and_of_map' : Π {n : ℕ} {P : fin n → Prop} (H : and_of_map P) (k : fin n), P k
/-| 0 P H (fin.mk val is_lt) := absurd is_lt (not_lt_zero _)
| 1 P H (fin.mk val is_lt) := have H1 : val = 0, from eq_zero_of_lt_one is_lt, begin revert is_lt, rw H1, intro, apply H  end
| (n+2) P H k := begin unfold and_of_map at H, unfold and_of_map_aux at H, end-/
:= sorry

theorem forall_of_and_of_map : Π {n : ℕ} {P : fin n → Prop} (H : and_of_map P) (k : fin n), P k
:=
sorry
/-| 0 P H k := absurd (fin.is_lt k) (not_lt_zero _)
| (m+1) P H k := begin
induction m,
{induction k,
unfold and_of_map at H,
assertv h1 : P (fin.mk 0 (lt_succ_self 0)) := H,
assertv h2 : val = 0 := sorry,
revert is_lt,
rw h2,
intro, apply h1},
{induction k,
cases decidable.em (val = a),
unfold and_of_map at H,
}
end-/

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
