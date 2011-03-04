(* Initialises rippling *)
Create HintDb cache discriminated.
Create HintDb ripple_basic discriminated.
Create HintDb ripple_cached discriminated.
Create HintDb simp discriminated.

Declare ML Module "rippling_plugin".

(* Hides wave annotation type parameters *)
Set Implicit Arguments.

(* Wave annotations (identity functions *)
Definition wave_out  := (fun (A:Type) (x:A) => x).
Definition wave_in   := (fun (A:Type) (x:A) => x).
Definition wave_hole := (fun (A:Type) (x:A) => x).
Definition wave_sink := (fun (A:Type) (x:A) => x).

(* Wave annotation notations *)
Notation "'__' x '__'" := (wave_hole x) (at level 20, right associativity) : type_scope.
Notation "<| x |>" := (wave_out  x) (at level 20, right associativity) : type_scope.
Notation ">| x |<" := (wave_in   x) (at level 20, right associativity) : type_scope.
Notation "& x &" := (wave_sink x) (at level 20, right associativity) : type_scope.

(* Ripples goal to a given *)
Ltac ripple_to given db :=
  let t := type of given in
  ripple t.

(* Ripples to a given, rewrites with given then makes attempt to solve goal *)
Ltac go given db :=
  ripple_to given db;
  rewrite given;
  tauto.

(* Displays embedding between assumption and goal *)
Ltac show_embeddings a :=
  let x := type of a in match goal with |- ?g => let y := type of g in embeds x g end.

(* Displays embedding between assumption and goal before and after tactic is applied (does not change goal) *)
Ltac embeds_after_tactic a t :=
  idtac "Before";
  show_embeddings a;
  try
  (t;
  idtac "After";
  show_embeddings a; fail).

(* Applies a tactic and displays embedding between assumption and goal before and after *)
Ltac embeds_after_tactic2 a t :=
  embeds_after_tactic a t;
  t.

Tactic Notation "ripple_progress" constr(a) tactic(t) := embeds_after_tactic2 a t.

Tactic Notation "embeds" constr(a) :=
  let x := type of a in match goal with |- ?g => let y := type of g in embeds x g end.

Tactic Notation "embeds_after_tactic" constr(a) tactic(t):=
 embeds_after_tactic a t.

Tactic Notation "embeds_after_tactic2" constr(a) tactic(t):=
 embeds_after_tactic2 a t.

Ltac rewrite_l2r_in R A := rewrite R in A.
Ltac rewrite_r2l_in R A := rewrite <- R in A.

(* Fertilises the only the term marked by __ __ markers *)
Ltac fert given dir :=
 let E := fresh in
 let T := fresh in

 (* Given has form ... -> x = y *)
 (* Goal should have the term x to fertilise into marked as __ x __ *)
 (* First we create an assumption of the form __ x __ = x *)
 (* Then we fertilise the RHS of this assumption to get __ x __ = y *)
 (* Then we fertilise the conclusion with this assumption *)
 (* This makes sure we only alter the parts of the conclusion we are meant to *)

match goal with | _ : _ |- context [__ ?t  __] =>
 assert (E : __ t __ = t); [reflexivity | idtac];

 (* Hide LHS of the assumption then fertilise it *)
 set (T := t) in E at 1;
 dir given E;

 subst T;
 rewrite E;
 clear E
 end.

Ltac fert_l2r given :=  fert given rewrite_l2r_in.
Ltac fert_r2l given :=  fert given rewrite_r2l_in.

(* Use given from l2r/r2l to rewrite every matching occurance
on lhs/rhs. *)
Ltac fert2_side given dir :=
 let E := fresh in
 let T := fresh in

  match goal with | _ : _ |- context [ ?lhs = ?rhs] =>
    match dir with
     false => set (T := rhs); rewrite given
   | true => set (T := lhs); rewrite <- given
  end;
subst T
end.

Ltac fert2 given := (fert2_side given false || fert2_side given true).


