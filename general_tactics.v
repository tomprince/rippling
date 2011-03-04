(* Automatically coerce bool terms to Prop terms when a Prop term is required *)
(* Coercion is_true (b:bool) : Prop := if b then True else False.*)
(* Do not hide function call added when coercion is used *)
(* Set Printing Coercion is_true.*)

Declare ML Module "rippling_plugin".
Require Import Omega.

(* Returns current goal *)
Ltac get_goal := match goal with |- ?g => g end.

(* Returns the head of a function application term *)
Ltac fun_name t :=
 match t with
 | ?f ?a ?b ?c ?d ?e => f
 | ?f ?a ?b ?c ?d => f
 | ?f ?a ?b ?c => f
 | ?f ?a ?b => f
 | ?f ?a => f
 | ?f => f (* FIXME: This will match anything! *)
 end.

(* try to solve the goal with a basic method *)
Ltac easy :=
  simpl in *;
  try subst; (* substs will fail if there is a non-recursive equality. It succeeds if it does nothing. *)
  reflexivity.

Ltac typeof x := let r:= (type of x) in let q:= (type of r) in q.

Ltac clear_rewrite x :=  rewrite x in *; clear x.
Ltac clear_rewrite2 x :=  rewrite <- x in *; clear x.

Ltac inject_subst x := injection x; intros; subst.

Ltac freshname name label :=
  let newname := fresh name label in newname.

(* Instanitates first meta variable *)
Ltac inst x := instantiate (1:=x).

Ltac elim_call c :=
(* Eliminate the function call *)
  case c;
   (* There will now be proj1_sig ( exists ... ) terms to simplify *)
   simpl proj1_sig in *;
   (* Introduce the sig type term and proof with nice names *)
   let a := fresh "sig_term0" in let b := fresh "sig_proof0" in
   intros a b;
   let f:= (fun_name c) in
   (* Try to eliminate the eliminated function call assumption *)
   try clear f;
   (* name the Set and Prop sig terms after the term they came from *)
   try rename_after a f "_s"; try rename_after b f "_p".

(* Eliminates inner most proj1_sig term in x *)
Ltac elim_inner_proj1 x :=
match x with
| context [proj1_sig ?c] =>
  (* Look for another match but use the current match if this fails. This finds the inner most match *)
  elim_inner_proj1 c ||
  elim_call c
end.

(* Eliminates all proj1_sig terms in goal. Useful when dealing with proof obligations produces by Program tactic. *)
Ltac elim_proj1 :=
  repeat elim_inner_proj1 get_goal.

Ltac destruct_proj1 := elim_proj1.

(* Performs destructs that are usually safe *)
Ltac safe_destruct :=
repeat match goal with
| [ H: ex ?x |- _] => destruct H
| [ H: ?x /\ ?y |- _] =>  destruct H
| [ H: prod ?x ?y |- _] => destruct H
| [ H: sig ?s |- _] =>
  (* FIXME: Want to rename terms after s, but can't... *)
  let a:= fresh in let b:= fresh in destruct H;
  (* (proj1_sig s) terms will now simplify *)
  simpl proj1_sig in *
end.

(* Try to find a contradiction with omega *)
Ltac absurd_omega :=
  solve [simpl in *; absurd (0 <> 0); omega].

(* Tries to prove absurdity by trying inversion on all assumptions to find one that's impossible to construct *)
Ltac absurd_inversion :=
match goal with
H:_ |- _ => inversion H; fail
end.

Ltac any_rewrite :=
match goal with
| [ H: ?x = ?y |- _] => idtac "rewrite" H ":" x "=" y; first [rewrite <- H | rewrite H]
end.

(* Easy inductive proof tactic. Tries to fertilise inductive step with any rewrites it finds *)
Ltac trivial_induction x :=
  induction x;
  simpl;
  try any_rewrite;
  simpl;
  reflexivity.

Ltac destruct_exists :=
match goal with
| |- ex ?x => econstructor
end.

Ltac tidy3 :=
  intros;
  try safe_destruct;
  simpl in *;
  try elim_proj1;
  simpl in *;
  subst;
  simpl in *.

Ltac tidy4 :=
  intros;
  repeat safe_destruct;
  elim_proj1;
  simpl in *;
  subst;
  simpl in *.

Ltac safe_tidy :=
  intros;
  elim_proj1;
  subst.
