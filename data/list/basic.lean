/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn

Basic properties of lists.
-/
import ...logic.basic ..nat.basic
open function nat

namespace list
universe variable uu
variable {α : Type uu}

/- theorems -/

@[simp]
lemma cons_ne_nil (a : α) (l : list α) : a::l ≠ [] :=
begin intro, contradiction end

lemma head_eq_of_cons_eq {α : Type} {h₁ h₂ : α} {t₁ t₂ : list α} :
      (h₁::t₁) = (h₂::t₂) → h₁ = h₂ :=
assume Peq, list.no_confusion Peq (assume Pheq Pteq, Pheq)

lemma tail_eq_of_cons_eq {α : Type} {h₁ h₂ : α} {t₁ t₂ : list α} :
      (h₁::t₁) = (h₂::t₂) → t₁ = t₂ :=
assume Peq, list.no_confusion Peq (assume Pheq Pteq, Pteq)

lemma cons_inj {α : Type} {a : α} : injective (cons a) :=
take l₁ l₂, assume Pe, tail_eq_of_cons_eq Pe

/- append -/

-- TODO(Jeremy): append_nil in the lean library should be nil_append

attribute [simp] cons_append nil_append

@[simp]
theorem append.assoc (s t u : list α) : s ++ t ++ u = s ++ (t ++ u) :=
begin induction s with a s ih, reflexivity, simp [ih] end

/- length -/

attribute [simp] length_cons

attribute [simp] length_append

/- concat -/

@[simp]
theorem concat_nil (a : α) : concat [] a = [a] :=
rfl

@[simp]
theorem concat_cons (a b : α) (l : list α) : concat (a::l) b  = a::(concat l b) :=
rfl

@[simp]
theorem concat_ne_nil (a : α) (l : list α) : concat l a ≠ [] :=
begin induction l, repeat { intro h, contradiction } end

attribute [simp] length_concat

@[simp]
theorem concat_append (a : α) (l₁ l₂ : list α) : concat l₁ a ++ l₂ = l₁ ++ a :: l₂ :=
begin induction l₁ with b l₁ ih, simp, simp [ih] end

theorem append_concat (a : α) (l₁ l₂ : list α) : l₁ ++ concat l₂ a = concat (l₁ ++ l₂) a :=
begin induction l₂ with b l₂ ih, repeat { simp } end

/- last -/

@[simp]
lemma last_singleton (a : α) (h : [a] ≠ []) : last [a] h = a :=
rfl

@[simp]
lemma last_cons_cons (a₁ a₂ : α) (l : list α) (h : a₁::a₂::l ≠ []) :
  last (a₁::a₂::l) h = last (a₂::l) (cons_ne_nil a₂ l) :=
rfl

theorem last_congr {l₁ l₂ : list α} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) (h₃ : l₁ = l₂) :
  last l₁ h₁ = last l₂ h₂ :=
by subst l₁

/- head and tail -/

@[simp]
theorem head_cons [h : inhabited α] (a : α) (l : list α) : head (a::l) = a :=
rfl

@[simp]
theorem tail_nil : tail (@nil α) = [] :=
rfl

@[simp]
theorem tail_cons (a : α) (l : list α) : tail (a::l) = l :=
rfl

/- list membership -/

attribute [simp] mem_nil_iff mem_cons_self mem_cons_iff


/- find -/

section find
variable [decidable_eq α]

@[simp]
theorem find_nil (a : α) : find a [] = 0 :=
rfl

theorem find_cons (a b : α) (l : list α) : find a (b::l) = if a = b then 0 else succ (find a l) :=
rfl

@[simp]
theorem find_cons_of_eq {a b : α} (l : list α) : a = b → find a (b::l) = 0 :=
assume e, if_pos e

@[simp]
theorem find_cons_of_ne {a b : α} (l : list α) : a ≠ b → find a (b::l) = succ (find a l) :=
assume n, if_neg n

@[simp]
theorem find_of_not_mem {l : list α} {a : α} : ¬a ∈ l → find a l = length l :=
list.rec_on l
   (suppose ¬a ∈ [], rfl)
   (take b l,
      assume ih : ¬a ∈ l → find a l = length l,
      suppose ¬a ∈ b::l,
      have ¬a = b ∧ ¬a ∈ l, begin rw [mem_cons_iff, not_or_iff] at this, exact this end,
      show find a (b::l) = length (b::l),
        begin rw [find_cons, if_neg this^.left, ih this^.right], reflexivity end)

lemma find_le_length {a : α} {l : list α} : find a l ≤ length l :=
list.rec_on l
  (by simp)
  (take b l, assume ih : find a l ≤ length l,
   show find a (b::l) ≤ length (b::l), from
     decidable.by_cases
       (suppose a = b, begin simp [this, find_cons_of_eq l (eq.refl b)], apply zero_le end)
       (suppose a ≠ b, begin simp [this, find_cons_of_ne l this], apply succ_le_succ ih end))

lemma not_mem_of_find_eq_length : ∀ {a : α} {l : list α}, find a l = length l → a ∉ l
| a []        := by simp
| a (b::l)    :=
  begin
    note h := decidable.em (a = b),
    cases h with aeqb aneb,
    { rw [find_cons_of_eq l aeqb, length_cons], intros, contradiction },
    rw [find_cons_of_ne l aneb, length_cons, mem_cons_iff, not_or_iff],
    intro h, split, assumption,
    exact not_mem_of_find_eq_length (nat.succ_inj h)
  end

lemma find_lt_length {a} {l : list α} (al : a ∈ l) : find a l < length l :=
begin
  apply lt_of_le_of_ne,
  apply find_le_length,
  apply not.intro, intro Peq,
  exact absurd al (not_mem_of_find_eq_length Peq)
end

end find

/- nth element -/

section nth

attribute [simp] nth_succ

theorem nth_eq_some : ∀ {l : list α} {n : nat}, n < length l → { a : α // nth l n = some a}
| ([] : list α) n h := absurd h (not_lt_zero _)
| (a::l) 0        h := ⟨a, rfl⟩
| (a::l) (succ n) h :=
  have n < length l, from lt_of_succ_lt_succ h,
  subtype.rec_on (nth_eq_some this)
    (take b : α, take hb : nth l n = some b,
      show { b : α // nth (a::l) (succ n) = some b },
         from ⟨b, by rw [nth_succ, hb]⟩)

theorem find_nth [decidable_eq α] {a : α} : ∀ {l : list α}, a ∈ l → nth l (find a l) = some a
| []     ain   := absurd ain (not_mem_nil _)
| (b::l) ainbl := decidable.by_cases
  (λ aeqb : a = b, by rw [find_cons_of_eq _ aeqb]; simp [nth, aeqb])
  (λ aneb : a ≠ b, or.elim (eq_or_mem_of_mem_cons ainbl)
    (λ aeqb : a = b, absurd aeqb aneb)
    (λ ainl : a ∈ l, by rewrite [find_cons_of_ne _ aneb, nth_succ, find_nth ainl]))

definition inth [h : inhabited α] (l : list α) (n : nat) : α :=
match (nth l n) with
| (some a) := a
| none     := arbitrary α
end

theorem inth_zero [inhabited α] (a : α) (l : list α) : inth (a :: l) 0 = a :=
rfl

theorem inth_succ [inhabited α] (a : α) (l : list α) (n : nat) : inth (a::l) (n+1) = inth l n :=
rfl

end nth

section ith

definition ith : Π (l : list α) (i : nat), i < length l → α
| nil       i        h := absurd h (not_lt_zero i)
| (a::ains) 0        h := a
| (a::ains) (succ i) h := ith ains i (lt_of_succ_lt_succ h)

@[simp]
lemma ith_zero (a : α) (l : list α) (h : 0 < length (a::l)) : ith (a::l) 0 h = a :=
rfl

@[simp]
lemma ith_succ (a : α) (l : list α) (i : nat) (h : succ i < length (a::l))
                      : ith (a::l) (succ i) h = ith l i (lt_of_succ_lt_succ h) :=
rfl
end ith

section taken

@[simp]
lemma taken_zero : ∀ (l : list α), taken 0 l = [] :=
begin intros, reflexivity end

@[simp]
lemma taken_nil : ∀ n, taken n [] = ([] : list α)
| 0     := rfl
| (n+1) := rfl

lemma taken_cons : ∀ n (a : α) (l : list α), taken (succ n) (a::l) = a :: taken n l :=
begin intros, reflexivity end

lemma taken_all : ∀ (l : list α), taken (length l) l = l
| []     := rfl
| (a::l) := begin change a :: (taken (length l) l) = a :: l, rw taken_all end

lemma taken_all_of_ge : ∀ {n} {l : list α}, n ≥ length l → taken n l = l
| 0     []     h := rfl
| 0     (a::l) h := absurd h (not_le_of_gt (zero_lt_succ _))
| (n+1) []     h := rfl
| (n+1) (a::l) h :=
  begin
    change a :: taken n l = a :: l,
    rw [taken_all_of_ge (le_of_succ_le_succ h)]
  end

-- TODO(Jeremy): restore when we have min
/-
lemma taken_taken : ∀ (n m) (l : list α), taken n (taken m l) = taken (min n m) l
| n         0        l      := sorry -- by rewrite [min_zero, taken_zero, taken_nil]
| 0         m        l      := sorry -- by rewrite [zero_min]
| (succ n)  (succ m) nil    := sorry -- by rewrite [*taken_nil]
| (succ n)  (succ m) (a::l) := sorry -- by rewrite [*taken_cons, taken_taken, min_succ_succ]
-/

lemma length_taken_le : ∀ (n) (l : list α), length (taken n l) ≤ n
| 0        l      := begin rw [taken_zero], reflexivity end
| (succ n) (a::l) := begin
                       rw [taken_cons, length_cons], apply succ_le_succ,
                       apply length_taken_le
                     end
| (succ n) []     := begin simp [taken, length], apply zero_le end

-- TODO(Jeremy): restore when we have min
/-
lemma length_taken_eq : ∀ (n) (l : list α), length (taken n l) = min n (length l)
| 0        l      := sorry -- by rewrite [taken_zero, zero_min]
| (succ n) (a::l) := sorry -- by rewrite [taken_cons, *length_cons, *add_one, min_succ_succ,
                                          length_taken_eq]
| (succ n) []     := sorry -- by rewrite [taken_nil]
-/
end taken

-- TODO(Jeremy): restore when we have nat.sub
/-
section dropn
-- 'dropn n l' drops the first 'n' elements of 'l'

theorem length_dropn
: ∀ (i : ℕ) (l : list α), length (dropn i l) = length l - i
| 0 l := rfl
| (succ i) [] := calc
  length (dropn (succ i) []) = 0 - succ i : sorry -- by rewrite (nat.zero_sub (succ i))
| (succ i) (x::l) := calc
  length (dropn (succ i) (x::l))
          = length (dropn i l)       : by reflexivity
      ... = length l - i             : length_dropn i l
      ... = succ (length l) - succ i : sorry -- by rewrite (succ_sub_succ (length l) i)
end dropn
-/

section count
variable [decidable_eq α]

definition count (a : α) : list α → nat
| []      := 0
| (x::xs) := if a = x then succ (count xs) else count xs

@[simp]
lemma count_nil (a : α) : count a [] = 0 :=
rfl

lemma count_cons (a b : α) (l : list α) :
  count a (b :: l) = if a = b then succ (count a l) else count a l :=
rfl

lemma count_cons' (a b : α) (l : list α) :
  count a (b :: l) = count a l + (if a = b then 1 else 0) :=
decidable.by_cases
  (suppose a = b, begin rw [count_cons, if_pos this, if_pos this] end)
  (suppose a ≠ b, begin rw [count_cons, if_neg this, if_neg this], reflexivity end)


@[simp]
lemma count_cons_self (a : α) (l : list α) : count a (a::l) = succ (count a l) :=
if_pos rfl

@[simp]
lemma count_cons_of_ne {a b : α} (h : a ≠ b) (l : list α) : count a (b::l) = count a l :=
if_neg h

lemma count_cons_ge_count (a b : α) (l : list α) : count a (b :: l) ≥ count a l :=
decidable.by_cases
  (suppose a = b, begin subst b, rewrite count_cons_self, apply le_succ end)
  (suppose a ≠ b, begin rw (count_cons_of_ne this), apply le_refl end)

-- TODO(Jeremy): without the reflexivity, this yields the goal "1 = 1". the first is from has_one,
-- the second is succ 0. Make sure the simplifier can eventually handle this.

lemma count_singleton (a : α) : count a [a] = 1 :=
by simp

@[simp]
lemma count_append (a : α) : ∀ l₁ l₂, count a (l₁ ++ l₂) = count a l₁ + count a l₂
| []      l₂ := begin rw [nil_append, count_nil, zero_add] end
| (b::l₁) l₂ := decidable.by_cases
  (suppose a = b, by rw [-this, cons_append, count_cons_self, count_cons_self, succ_add,
                         count_append])
  (suppose a ≠ b, by rw [cons_append, count_cons_of_ne this, count_cons_of_ne this, count_append])

@[simp]
lemma count_concat (a : α) (l : list α) : count a (concat l a) = succ (count a l) :=
by rw [concat_eq_append, count_append, count_singleton]

lemma mem_of_count_pos : ∀ {a : α} {l : list α}, count a l > 0 → a ∈ l
| a []     h := absurd h (lt_irrefl _)
| a (b::l) h := decidable.by_cases
  (suppose a = b, begin subst b, apply mem_cons_self end)
  (suppose a ≠ b,
   have count a l > 0, begin rw [count_cons_of_ne this] at h, exact h end,
   have a ∈ l,    from mem_of_count_pos this,
   show a ∈ b::l, from mem_cons_of_mem _ this)

lemma count_pos_of_mem : ∀ {a : α} {l : list α}, a ∈ l → count a l > 0
| a []     h := absurd h (not_mem_nil _)
| a (b::l) h := or.elim h
  (suppose a = b, begin subst b, rw count_cons_self, apply zero_lt_succ end)
  (suppose a ∈ l, calc
   count a (b::l) ≥ count a l : count_cons_ge_count _ _ _
           ...    > 0         : count_pos_of_mem this)

lemma mem_iff_count_pos (a : α) (l : list α) : a ∈ l ↔ count a l > 0 :=
iff.intro count_pos_of_mem mem_of_count_pos

@[simp]
lemma count_eq_zero_of_not_mem {a : α} {l : list α} (h : a ∉ l) : count a l = 0 :=
have ∀ n, count a l = n → count a l = 0,
  begin
    intro n, cases n,
     { intro this, exact this },
    intro this, exact absurd (mem_of_count_pos (begin rw this, exact dec_trivial end)) h
  end,
this (count a l) rfl

lemma not_mem_of_count_eq_zero {a : α} {l : list α} (h : count a l = 0) : a ∉ l :=
suppose a ∈ l,
have count a l > 0, from count_pos_of_mem this,
show false, begin rw h at this, exact nat.not_lt_zero _ this end

end count
end list
