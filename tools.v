(* Setup file for all proof automation tools and other useful things *)
Declare ML Module "recdef_plugin".
Declare ML Module "rippling_plugin".
Require Import List.
Require Export Syntax. (* put after "Import List" for [1;2] style list notation *)
Require Import Program.
Require Import Setoid.
Require Import Bool.
Require Import Omega.
Require Import Arith.Compare_dec.

Notation nat_eq_dec := eq_nat_decide.
Notation bool_eq_dec := bool_dec.

(* Test lots of examples; useful for when not finding a counterexample is
expensive e.g. not identifying a program error for the user. Gives counterexample trace *)
Ltac qc := intros; quickcheck 0 50 0 1.
(* Check only a few examples with tracing off; useful for when a brief check is good enough
e.g. after generalisation when it's usually easy to find counterexamples, as
long as there are no side-conditions. Setting this too low can cause
non-theorems to slip thru, too high and testing takes up more time *)
Ltac fast_qc := intros; quickcheck 0 20 0 0.
(* Checks more examples and gives no trace *)
Ltac qc_no_trace := intros; quickcheck 0 50 0 0.

Goal True.
(* Quickcheck generators for common types *)
Generator (forall x y:nat, {x=y}+{x<>y}) [eq_nat_decide].
Generator (forall x y:bool, {x=y}+{x<>y}) [bool_dec].
Generator (nat -> nat) [S].
Generator (nat -> nat -> nat) [plus; mult].
Admitted.

Load "general_tactics.v".
Load "rippling.v".
Load "unit_testing.v".

(* Removes ` notation for proj1_sig *)
(*Notation "'proj1_sig' x" := (proj1_sig x) (at level 10).*)

(*
(* Turn off Program tactic proof automation *)
Obligations Tactic := idtac.
*)

(*
From: http://www.lix.polytechnique.fr/cocorico/if/then/else (tactical)
"if t then t1 else t2 is equivalent to t; t1 if t does not fail and is equivalent to t2 otherwise."
*)
Tactic Notation
  "if" tactic(t)
  "then" tactic(t1)
  "else" tactic(t2) :=
   first [ t; first [ t1 | fail 2 ] | t2 ].

(* Succeeds if c is a constant. c must be a constructor call with only
   other constructors or type variables as parameters *)
(* Extra fails are to stop backtracking on outer "match" *)
Ltac constant c :=
idtac;
  match c with
  | ?f ?x => idtac ;
     first [constant f | fail 2];
     first
     [
        constant x
     |
        let t := type of x in
        match t with
        | Type => idtac
        | _ =>  fail
        end
     | fail 2]
 | ?x => is_constructor x
 | _ => fail 1
end.

Ltac constant_lhs := match goal with |- ?x = ?y => constant x end.
Ltac constant_rhs := match goal with |- ?x = ?y => constant y end.


(* Reverts all assumptions. Useful to do this so you can copy/paste the current goal as the conjecture for a new named lemma. *)
Ltac revert_all := repeat match goal with [ H : _ |- _ ] => revert H end.

(* Displays current goal in a format that can be copy/pasted as a stand alone lemma declaration e.g. Goal (forall x, x = x + 0). *)
Ltac print_goal :=
  try (revert_all; let g := get_goal in idtac "Copy/paste this to declare as a stand alone lemma:"; idtac "Goal"g"."; fail).

(* Clears all assumptions that mention variable "x" *)
Ltac clear_dep_ass x := match goal with H : context [ x ] |- _ => clear H end.

(* For each assumption R, if R can be used in any direction as a rewrite rule, this tactic does so then clears the assumption  *)
Ltac use_equations :=
  repeat match goal with
  [ R: _ |- _ ] => (rewrite R in * || rewrite <- R in *); clear R; idtac "Used and discarded equation: " R
  end.

(* Like subst, but does not fail when it finds a recursive equation *)
Ltac sub := repeat (match goal with x : _ |- _ => subst x end).

(* Creates a new subgoal that is a copy of the current goal. This is useful
if you e.g. want to write a hand proof and an automated proof of a theorem
for testing or demonstration reasons. *)
Ltac copy :=
  match goal with
 [ |- ?g ] => let f := fresh in cut g; [intro f;clear f | idtac]
 end.

(* Uses injection to simplify then (if possible) discard any equational assumptions *)
Ltac auto_injection :=
  repeat
    match goal with
    [ H : ?x = ?y |- _ ] =>
      injection H;
      match goal with
      (* Original equation appears in conclusion if injection could not simplify it *)
      | [ |- x = y -> _ ] => fail 1
      |   _                     => let I := fresh in intro I; try clear H
      end
    end.

Goal forall x y, S(x+1) = S(y+1) -> S x = S y -> True.
intros.
auto_injection.
auto_injection.
Admitted.

Ltac auto_discriminate :=
  match goal with
  [ H : ?x = ?y |- _ ] => discriminate H
  end.

Goal 1 = 0 -> True.
intros.
auto_discriminate.
Defined.

(* Clears, if possible, unuseful equations of the form n = n *)
Ltac remove_n_eq_n :=
  repeat progress
  match goal with
  [ H : ?n = ?n |- _ ] => clear H
  end.

Ltac general :=
  intros; generalise_goal; qc.

Ltac rip := ripple.
Ltac gen := generalise_goal; intros; irrelevant.

Create HintDb cache discriminated.
Create HintDb ripple discriminated.
Create HintDb simp discriminated.

(* destructs any proj1_sig terms in hypotheses *)
Ltac destruct_proj1_hyp :=
  repeat
  match goal with
    H := context [proj1_sig ?R]  |- _ =>
      let p := fresh "p" in
      let s := fresh "s" in
      destruct R as [s p];
      simpl proj1_sig in H
   | _ => fail 1
   end.

(* Eliminates (proj1_sig r) when this proof obligation was generated when
   defining r. Works by assuming there will be an assumption with the name "r"
   in the goal *)
Ltac elim_rec_proj1 :=
  match goal with
   |- context [ proj1_sig ?c] =>
      elim_call c;
      let f := fun_name c in
      clear f (* will fail if f is not an assumption *)
  end.

Ltac recursive_call :=
  sub; (* subtitute pattern matching equations *)
  elim_rec_proj1;
  ripple.

(* Simplifies initial Program tactic proof obligations without destroying any
embeddings *)
Ltac tidy :=
  (* destruct calls to functions that return subset types *)
  destruct_proj1;
  destruct_proj1_hyp;
  (* Boby of assumptions like "v := s : list t * list t" is lost if they are
  destructed. substs these first *)
  sub;
  (* destruct subset types and others *)
  safe_destruct;
  sub.

(* A basic simplification tactic *)
Ltac simp_basic' :=
 simpl in *;
 unfold not; (* change ~P into P -> False *)
 intros; (* must intro a var before "case" can be called on it *)
 try case_concl; (* this can introduce implications and equations to the conclusion *)
 intros;
 try sub;
 try split;
 try auto_injection.

Ltac simp_basic := repeat progress simp_basic'.

Print HintDb core.

Hint Resolve conj @eq_refl eq_sym : cache.

Ltac triv' :=
  try tauto;
  try auto_discriminate;
  try absurd_inversion
(*  ;try omega*)
  .

(* A fast tactic to solve goals that do not need induction
   (cached lemma usage factored out for testing reasons) *)
Ltac triv :=
  triv';
  (* prove with "trivial". simpl first because only exact matches allowed *)
  let t := auto_without_core  with cache in (* don't use core *)
  (* let t := trivial with cache in (* use core too *) *)
  try solve [simpl; t]
  .

Ltac simp' :=
  tidy;
  repeat progress
  (
    simp_basic;
    try use_equations (* try this last as this is unsafe and should be avoided *)
  )
  ; remove_n_eq_n (* remove n = n equations as these can be identified as pointless ripple targets *)
  .

(* A simplification tactic that performs case splits and uses autorewrite db *)
Ltac simp :=
  simp'
  ; try (autorewrite with simp) (* need try because db might not exist *)
  .

(* Inverse functionality (e.g. S x = S y => x = y), restricted to when only one
   subgoal is generated (e.g. this avoids x + y = y + x => x = y /\ y = x).
 *)
Ltac f_simp :=
  repeat progress (simple apply f_equal).

(* default solver configuration *)
Ltac dt := super 5 (triv) (simp) (fast_qc) 1 with ripple_basic ripple_cached.
(* same but without quickcheck (useful when you expect quickcheck to take too long) *)
Ltac dn := super 5 (triv) (simp) (idtac) 1 with ripple_basic ripple_cached.
(* basic solver that never uses cached lemmas *)
Ltac d' := super 5 (triv') (simp') (fast_qc) 0 with ripple_basic.
(* default solver plus initial descriptive counterexample check *)
Ltac d :=
  sub (*remove pattern matching equations first first to help quickcheck*);
  qc;
  try recursive_call; (* try recursive call proof pattern first *)
  dt.
Ltac ps := tidy; d.

Tactic Notation "ind0" := induction_nth 0.
Tactic Notation "ind1" := induction_nth 1.
Tactic Notation "ind2" := induction_nth 2.
Tactic Notation "ind3" := induction_nth 3.
Tactic Notation "ind4" := induction_nth 4.

Tactic Notation "indr1" :=
  induction_nth 1; try (simp;triv;fail); try ripple.
Tactic Notation "indr0" :=
  induction_nth 0; try (simp;triv;fail); try ripple.
Tactic Notation "indr2" :=
  induction_nth 2; try (simp;triv;fail); try ripple.
Tactic Notation "indr3" :=
  induction_nth 3; try (simp;triv;fail); try ripple.
Tactic Notation "indr4" :=
  induction_nth 4; try (simp;triv;fail); try ripple.

Ltac should_solve := solve_or_admit d.
(* Tries to prove a lemma and add it as a rippling hint *)
Ltac hint' lemma solver :=
	let C := fresh "c" in
	assert (C : lemma);
	[clear;
        (* This line only needed if solver does not cache e.g. if omega/admit was used.
           Otherwise, lemma will be cached twice if used *)
	(* lemma_cache *)
        solver | idtac; clear C].
Ltac hint lemma := hint' lemma d.

Ltac case_split := case_concl; intros; sub.

Load "discover.v".