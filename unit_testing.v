(* Useful functions for unit testing Coq scripts *)

(* Make the printing width bigger so longer unit test output line are not broken up *)
Set Printing Width 300.

(* Used to abandon the current goal in tests *)
Ltac admitted := idtac "************ GOAL ADMITTED ************"; admit.

(* Display unit test success message *)
Ltac unit_success_message :=
  match goal with
    [|- ?g] => idtac;idtac "<successtest goal='" g "'/>"
  end.

(* Display unit test fail message *)
Ltac unit_fail_message :=
  match goal with
    [|- ?g] => idtac;idtac "*** FAILURE: <failedtest goal='" g "'/>"
  end.

(* If t succeeds display success message, otherwise display failure message. *)
Ltac unit_succeeds t :=
  try ((t; unit_success_message; fail 1) || unit_fail_message).

(* Fails if goal is not equal to g *)
Ltac goal_equals g:=
  match goal with
    [|-g] => idtac
  | [|-?m] => fail
  end.

(* Checks goal equals g *)
Ltac assert_goal g:=
  match goal with
    [|-g] => unit_success_message
  | [|-?m] => unit_fail_message; idtac "<message>Goal is "  " when it is expected to be " g ".</message>"
  end.

(* Unit test succeeds if tactic fails *)
Tactic Notation "assert_fail" tactic(t) := try ((t; unit_fail_message; idtac "<message>Tactic succeeded when it was expected to fail.</message>"; fail 1) || unit_success_message).

(* Unit test succeeds if tactic succeeds *)
Tactic Notation "assert_success" tactic(t) := try ((t; unit_success_message;fail 1) || unit_fail_message).

(* Expects t to succeed and changes the goal to g. This tactic does not modify the proof state. *)
Tactic Notation "assert_result" tactic(t) constr(g) :=
  try ((t;
  match goal with
    [|-g] => unit_success_message; fail 2
  | [|-?m] => unit_fail_message; idtac "<message>Goal is " m " when it is expected to be " g ".</message>"; fail 2
  end) || (unit_fail_message; idtac "<message>Tactic call failed when it was expected to succeed</message>")).

(*
Goal True.
assert_result (fail) (True).
assert_result (fail) (False).
assert_result (idtac) (True).
assert_result (idtac) (False).
Admitted.
*)

Ltac solve_or_admit t :=
(* Hack: creates a new goal the same as the current one, displays success if t solves this,
   then admits the original goal. This trick is needed display the success message when t
   solves as tactic execution stops when the proof is finished. *)
(match goal with [|- ?g] => assert g;[t | unit_success_message; assumption] end)
||
(unit_fail_message; admitted).
Tactic Notation "solve_or_admit" tactic(t) := solve_or_admit t.

(* Succeds when assumption is present in the current list of assumptions. *)
(* FIXME: "type of" will succed if the goal contains a variable called _unused_name
  (i.e. not the name you pass to the tactic, the actual name "_usued_name"!). Using
  obscure parameter name to avoid this bug. *)
Ltac present _unused_name := try ((let t := type of _unused_name in fail 1) ||
  fail 1 "<message>Assumption " _unused_name " was was unexpectedly missing.</message>").

(* Succeeds when assumption is missing in the current list of assumptions *)
Ltac missing a :=
  try (present a; fail 1 "<message>Assumption " a " was was unexpectedly present.</message>").

Ltac unit_missing a := let t:= missing a in assert_success t.
Ltac unit_present a := let t:= present a in assert_success t.

