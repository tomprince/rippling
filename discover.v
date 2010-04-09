(* Some testing on auto discovering obvious lemmas for operators from templates *)

Require Import Omega.

Ltac solver2 := admit. (* a very reliable solver! *)
Ltac solver := d.

(* Tries to prove and cache a conjecture using a tactic *)
Ltac discover3 conjecture prover :=
idtac "Trying to prove" conjecture;
assert conjecture; clear;
[
  let lemma_name := fresh "discovered" in
  (* Trick: New goal created after conjectured subgoal. If the proof progresses
  to proving the second subgoal, we know the conjecture has been proven *)
  cut True;
  [
    intro; clear;
      abstract prover  lemma_name
    |
    let t := type of lemma_name in
    idtac "discovered " lemma_name " : "t;
    constructor
  ]
|
  idtac].

Ltac discover2 conjecture :=
  let prover := (intros; solver) in
try (if assert conjecture; clear;
qc_no_trace
then
fail
else
  (*idtac "discover: Counterexample found! ";*)
  fail 2);
  idtac "discover: Trying to prove ";
  hint' conjecture prover;
  idtac "discover: *********************************** Proven! " conjecture.

Ltac get_base t :=
match t with
  nat => 0
| list _ => nil
end.

(*(* need base case values *)

(* identity element *)
try discover2 (forall x, op x b = x);
try discover2 (forall y, op b y = y);

(* absorbing element *)
try discover2 (forall x, op x b = b);
try discover2 (forall y, op b y = b);

try discover2 (op b = b);
*)

Ltac discover f :=
(* f = arity 1 *)
(* involution *)
try discover2 (forall x, f (f x) = x);
(* injectivity *)
(*try discover2 (forall x y, f x = f y <-> x = y);*)
(* TODO: need to do a check that f is not being used in curried form match f x => *)

(* f = arity 2 *)
(* commutativity *)
try discover2 (forall x y, f x y = f y x);
(* associativity *)
try discover2 (forall x y z, f (f x y) z = f x (f y z))

(* associativity varients *)
(*try discover2 (forall x y z, f (f x y) z = f x (f z y));
try discover2 (forall x y z, f (f x y) z = f y (f x z));
try discover2 (forall x y z, f (f x y) z = f y (f z x));
try discover2 (forall x y z, f (f x y) z = f z (f x y));
try discover2 (forall x y z, f (f x y) z = f z (f y x));
try discover2 (forall x y z, f (f x y) z = f (f y x) z)*)
.

Ltac discoverfg f g :=
(* f = arity 2 *)
(* g = arity 2 *)
try discover2 (forall x y z, f x (g y z) = g (f x y) (f x z));
try discover2 (forall x y z, f (g y z) x = g (f y x) (f z x));

(* f = arity 2 *)
(* g = arity 1 *)
try discover2 (forall x y, f x (g y) = f (g x) (y));
try discover2 (forall x y, f x (g y) = g (f x y));
try discover2 (forall x y, g (f x y) = f (g x) (g y));
try discover2 (forall x, g (f x) = g (x))
.

Ltac discoverfgh' f g h :=
idtac "discover" f g h;
(* f = arity 2 *)
(* g = arity 2 *)
try discover2 (forall x y z, f (g x y) = h (f x) (f y)).

Ltac discoverfgh f g h :=
discoverfgh' f g h;
discoverfgh' f h g;
discoverfgh' g f h;
discoverfgh' g h f;
discoverfgh' h f g;
discoverfgh' h g f.

Ltac discoverb f g :=
try discoverfg f g;
try discoverfg g f.

Ltac discover_with_1 pairs :=
(*idtac "discover: pair" pairs;*)
  match pairs with
  | [] => idtac
  | (?f=_)::?t => try discover f; discover_with_1 t
  end.

Ltac discover_with_pair2 pairs :=
(*idtac "discover: pair" pairs;*)
  match pairs with
  | [] => idtac
  | (?h=_, (?f=_, ?g=_))::?t =>
  try discoverfgh f g h; discover_with_pair2 t
  end.

Ltac discover_with_pair pairs :=
(*idtac "discover: pair" pairs;*)
  match pairs with
  | [] => idtac
  | (?f=_, ?g=_)::?t => try discoverb f g; discover_with_pair t
  end.

Ltac discoverL functions :=
idtac "discover:";
idtac "discover: starting discovery process";
  let pairs := eval simpl in (list_prod functions functions) in
  discover_with_pair pairs;
  let pairs2 := eval simpl in (list_prod functions pairs) in
  discover_with_pair2 pairs2;
  discover_with_1 functions.
Ltac idt d := idtac d;discover2 d.
Ltac appass f :=
idt (forall x, f (f x) = x).

(*
Goal forall(T:Type), True. intros.
ReplaceInTests T nat.
discover mult.
discover plus.
discoverL
[app(A:=T)=app(A:=T);
length(A:=T)=length(A:=T);
plus=plus].
discoverL
([app(A:=T)=app(A:=T);
rev(A:=T)=rev(A:=T);
length(A:=T)=length(A:=T);
mult=mult;
plus=plus;
S=S;
cons (A:=T)=cons (A:=T);
postorder (A:=T)=postorder (A:=T);
inorder (A:=T)=inorder (A:=T);
preorder (A:=T)=preorder (A:=T);
postorder (A:=T)=postorder (A:=T);
mirror (A:=T)=mirror (A:=T);
(*min =min ;
max =max ;*)
height (A:=T)=height (A:=T);
num_nodes (A:=T)= num_nodes (A:=T)
]).
*)
