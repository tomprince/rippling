(*

This demo script demonstrates new tactics for inductive proof automation for Coq. The
automation can be used to discharge goals that involve inductively defined data types
and recursively defined functions. This includes proofs that involve case splitting and
multiple inductive hypotheses. We give examples of proofs involving trees, lists,
higher-order functions and Peano arithmatic.

The main features of the automation are as follows:

- A tactic that implements "rippling". Rippling is used to control the use of rewrite
  rules in step case goals of inductive proofs. See the following FAQ for a
  general overview of rippling:
  http://dream.dai.ed.ac.uk/projects/ripple-faq.html

- Automated generalisation heuristics.

- Techniques for caching lemmas found during proof search and reusing these
  lemmas in future proof attempts.

- A QuickCheck-like counterexample finder.

More documentation be found on:
http://homepages.inf.ed.ac.uk/s0091720/

The automation is composed of the following modular tactics:

- simp: Attempts to simplify the current goal. Briefly, this is done by normalising
  the goal, using and discarding any equational assumptions, performing case splits
  when there are subterms of the form "match x..." and exhaustively rewriting with
  a set of rules chosen simplification.

- triv: Tries to prove the current goal outright using "tauto" and cached lemmas.

- ind0/ind1/ind2/...: Begins an inductive proof on the nth variable in the conclusion.
  Universal introduction and reintroduction is performed prior to induction so as to
  strengthen the inductive hypotheses.

- ripple: Identifies assumptions that share syntactic similiarities with the conclusion
  and succeeds when the conclusion can be modified so that these assumptions can be used
  to rewrite the conclusion.

- gen: Attempts to generalise the current goal.

- qc: Succeeds when it cannot ﬁnd a counterexample to the current goal.

The top-level tactic which makes use of these tactics is called "d" (we really need
a better name for this!). The ripple', simp', triv' and d' tactics are versions
of the above tactics that do not use cached lemmas and only rely on basic definitions.

*)

(********************************************************************************)
(* Overview                                                                     *)
(********************************************************************************)

(*
First, we use an example proof to give an overview of the general search strategy
used by the top-level proof automation. This proof only involves the use of basic
definitions, where the automation is able to conjecture the needed lemmas.

Note: Open this script in CoqIDE launched from a console. The console will contain
useful proof search feedback.
*)

Require Import tools.
Require Import discover.

Require Import List.
Require Export Syntax. (* put after "Import List" for [1;2] style list notation *)
Require Import Program.
Require Import Setoid.
Require Import Bool.
Require Import Omega.
Require Import Arith.Compare_dec.

Set Implicit Arguments.

(*
Before using the "ripple" tactic, we must call the "AddWaveRule" command on each
function definition we are going to use in our script. This command generates basic
equations from function definitions for use as rewrite rules by "ripple" tactic.
*)
AddWaveRule app.
AddWaveRule rev.

Goal forall (A:Type) (x y:list A), rev (x ++ y) = rev y ++ rev x.

(* The automation first attempts a trivial proof by calling "simp" and "triv" in
sequence. No progress is made here. *)
simp'; triv'.

(* If this fails, an attempt is made to generalise the goal. Backtracking to the
point before generalising the goal is allowed. No generalisation is found here. *)
try gen.

(* Induction is then performed on some variable in the goal. If the inductive proof
fails, induction is attempted on another variable until all choices are exhausted. *)
ind2.

 (* Step cases are attempted first *)
 Focus 2.
 (* When a goal contains assumptions that have syntactic similarities to the conclusion,
 rippling is used is rewrite the conclusion so that these assumptions can be used to
 rewrite the conclusion. Rippling must succeed to continue.

 Rippling succeeds in this case. See the console output to see how rippling moves
 the terms in the conclusion that are  different to the inductive hypothesis
 (coloured green) towards the top of the term tree of the conclusion until the
  inductive hypothesis can be used to rewrite the conclusion *)
 ripple'.

 (* The strategy above is followed on each of the remaining goals to finish the proof *)
 simp'; triv'.
 (* This time, two common subterms ("rev y" and "rev l") are identified and generalised. *)
 gen.

 ind0.
   (* Step case *)
   Focus 2.
   ripple'.
   simp'; triv'.

   (* Base case *)
   Focus 1.
   simp'; triv'.

 (* Base case *)
 simp'; triv'.
 gen.
 ind0.
   Focus 2.
   (* Step case *)
   ripple'.
   simp'; triv'.

   (* Base case *)
   simp'; triv'.
Qed.

(*
Here, we prove the same goal again but with the top-level proof automation tactic.
Look at the standard output from your console after the tactic call to see the
trace of the proof search, where the indentation represents search depth.
*)
Goal forall (A:Type) (x y:list A), rev (x ++ y) = rev y ++ rev x.
d'.
Qed.

(* We now give several examples of proofs that can be fully automated from only
basic definitions *)

(********************************************************************************)
(* Arithmatic theorem examples                                                  *)
(********************************************************************************)

Fixpoint pow (r:nat) (n:nat) {struct n} : nat :=
   match n with
   | O => 1
   | S n => r * pow r n
   end.
Infix "^" := pow : type_scope.

AddWaveRule plus.
AddWaveRule pow.
AddWaveRule mult.

Goal forall x y, x + y = y + x.
d'.
Qed.

Goal forall x y, x * y = y * x.
d'.
Qed.

Goal forall x y z, x * (y + z) = x * y + x * z.
d'.
Qed.

Goal forall x n m, x ^ (n + m) = x ^ n * x ^ m.
d'.
Qed.

(********************************************************************************)
(* List theorem examples                                                        *)
(********************************************************************************)

AddWaveRule length.

Goal forall (A:Type) (x y z:list A), (x ++ y) ++ z = x ++ y ++ z.
d'.
Qed.

Goal forall (A:Type) (a b:list A), length (a ++ b) = length a + length b.
d'.
Qed.

Goal forall (A:Type) (a:list A), length (rev a) = length a.
d'.
Qed.

Goal forall (A:Type) (a:list A), rev (rev a) = a.
d'.
Qed.

Goal forall (A:Type) (x y:list A), rev (x ++ y) = rev y ++ rev x.
d'.
Qed.

(********************************************************************************)
(* Higher-order theorem examples                                                *)
(********************************************************************************)

Fixpoint sum (a:list nat) : nat :=
  match a with
  | [] => 0
  | h :: t => h + sum t
  end.

AddWaveRule sum.
AddWaveRule seq.
AddWaveRule fold_left.
AddWaveRule map.

Goal forall (a:list nat), fold_left plus a 0 = sum a.
d'.
Qed.

Goal forall (A B:Type) (f:A -> B) (x y:list A), map f (x ++ y) = map f x ++ map f y.
d'.
Qed.

Goal forall (A B:Type) (f:A -> B) (x y:list A),
  rev (map f (x ++ y)) = rev (map f y) ++ rev (map f x).
d'.
Qed.

Goal forall len start, map S (seq start len) = seq (S start) len.
d'.
Qed.

(********************************************************************************)
(* Binary tree theorem examples                                                 *)
(********************************************************************************)

Section BTree.
Variable A : Type.

Inductive btree : Type :=
| empty : btree
| node : A -> btree -> btree -> btree.
End BTree.

Implicit Arguments empty [A].
Notation "'leaf' x" := (node x (empty) (empty)) (at level 20).

Section BTreeFunctions.
Variable A : Type.

Fixpoint num_nodes (a : btree A) : nat :=
  match a with
  | empty => 0
  | node v l r => S ((num_nodes l) + (num_nodes r))
  end.

Fixpoint mirror (a : btree A) : btree A :=
  match a with
  | empty => empty
  | node v l r => node v (mirror r) (mirror l)
  end.

Fixpoint inorder (a:btree A) : list A :=
  match a with
  | empty => []
  | node v l r => (inorder l) ++ [v] ++ (inorder r)
  end.

Fixpoint postorder (a : btree A) : list A :=
  match a with
  | empty => []
  | node v l r => (postorder l) ++ (postorder r) ++ [v]
  end.

Fixpoint preorder (a : btree A) : list A :=
  match a with
  | empty => []
  | node v l r => v::((preorder l) ++ (preorder r))
  end.
Require Import Arith.Max.

Fixpoint height (a : btree A) : nat :=
  match a with
  | empty => 0
  | node v l r => 1 + max (height l) (height r)
  end.
End BTreeFunctions.

AddWaveRule num_nodes.
AddWaveRule mirror.
AddWaveRule postorder.
AddWaveRule preorder.
AddWaveRule inorder.
AddWaveRule height.
AddWaveRule max.

(* In these proofs, the "ripple" tactic must consider two inductive hypotheses
in step cases goals *)

Goal forall (A:Type)(a : btree A), mirror (mirror a) = a.
d'.
Qed.

Goal forall (A:Type)(a : btree A), height (mirror a) = height a.
d'.
Qed.

Goal forall (A:Type)(a : btree A), postorder (mirror a) = rev (preorder a).
d'.
Qed.

Goal forall (A:Type)(a : btree A), length (inorder a) = num_nodes a.
d'.
Qed.

(********************************************************************************)
(* Case splitting examples                                                      *)
(********************************************************************************)

(* In these examples, case splits are required during step case proofs *)

Variable A:Set.
Variable leA : relation A.
Variable eqA : relation A.
Hypothesis eqA_dec : forall x y:A, {x = y} + {x <> y}.
Hypothesis leA_dec : forall x y:A, {leA x y} + {leA y x}.

AddWaveRule count_occ.
Notation l_perm x y :=
  (forall n, count_occ eqA_dec x n = count_occ eqA_dec y n) (only parsing).

Goal forall x y, max x y = max y x.
d'.
Qed.

Goal forall x y z, max x (max y z) = max (max x y) z.
d'.
Qed.

Goal forall x y, l_perm (x ++ y) (y ++ x).
d'.
Qed.

Goal forall x, l_perm (rev x) x.
d'.
Qed.

(* Properties of insertion sort *)

Fixpoint insert (x:A) (a:list A) : list A :=
  match a with
  | nil => [x]
  | h::t => if leA_dec x h then x::a else h::(insert x t)
  end.

Fixpoint insertion_sort (a:list A) : list A :=
  match a with
  | nil => []
  | h::t => insert h (insertion_sort t)
  end.

AddWaveRule insert.
AddWaveRule insertion_sort.

Goal forall a, length (insertion_sort a) = length a.
d'.
Qed.

Goal forall a, l_perm (insertion_sort a) a.
d'.
Qed.

(*

Limitations:

- The proof automation does not offer much support for goals involving inductive
predicates (e.g. "<", "In") at the moment.

- The conclusion of the goal must generally be an equation. We hope to support
user-defined relations in the future.

- We do not currently support proofs that require piecewise fertilisation. This
is needed when the inductive hypothesis contains an implication, such as when
induction is performed on "x" in the following goal:

forall x y z, list perm (x ++ y) z -> length x < S (length z)

*)

(********************************************************************************)
(* Lemma caching                                                                *)
(********************************************************************************)

(* All inductive proofs are cached for reuse in later proof attempts. A single proof
can involve several inductive proofs. We find cached lemmas are typically general
and reusable. For example:
*)

Goal forall x y, x * y = y * x.
d.
Qed.

(* Lemmas cached:
forall x y, x * y = y * x
forall x y z, x + (y + z) = y + (x + z))
forall x y, x * S y = x + x * y
forall x, x * 0 = 0
*)

Goal forall (A:Type) (x y:list A), rev (x ++ y) = rev y ++ rev x.
d.
Qed.

(*
Lemmas cached:
forall x y, rev (x ++ y) = rev y ++ rev x
forall (A::Type) (x y z:list A), (x ++ y) ++ z = x ++ y ++ z
forall (A:Type) (x:list A0), x = x ++ []
forall (A:Type) (x y:list A0), rev (x ++ y) = rev y ++ rev x
*)

(*
All cached lemmas are inserted into the "cache" database for use by the "triv" tactic.
*)
Print HintDb cache.

(*
Most cached lemmas are inserted into the "ripple_cached" database for use by the
"ripple" tactic. We do not add rules that only serve to make rippling less efficient:
the rule "X = Y" is not added as a left-to-right rewrite rule when X is a ground
term or when Y can be decorated with terms so that Y is the same term as X.
*)

PrintHints ripple_cached.

(*
The "ripple_basic" database contains only the rules added by "AddWaveRule" and is
used by the "ripple" tatic. This is for when we only want to make use of basic
definitions when searching for proofs.
*)
PrintHints ripple_basic.

(*
Rewrite rules that can be used for simplification are inserted into the "simp"
database for use by the "simp" tactic. When caching proofs, the equation X = Y
will be automatically added as a left-to-right simplification rule when either
of the following are true:

1) Y is a ground term e.g. (forall x * 0 = 0), (forall x, min x 0 = 0)

2) terms can be added to Y such that X is the same term as Y
   e.g. (forall x, x ++ [] = x), (forall x, rev (rev x)),
   (forall f a, length (map f a) = length a)

We find this heuristic is good at identifying obvious simplification rules.
*)
PrintHints simp.

(*
The reuse of cached lemmas can increase proof converage and make proof search
more effecient. For example:
*)

Goal forall (A:Type) (x y:list A), rev ((rev x) ++ y) = rev y ++ x.
(* A proof without using cached lemmas fails here *)
try d'.

(* Cached lemmas are helpful when proving this goal by induction on "x" *)
ind2.
 (* Step case *)
 Focus 2.
 (* Rippling without cached lemmas fails here *)
 try ripple'.
 (* Rippling with the cached lemmas from above succeeds, with the
    use of the lemma for associativity of ++. *)
 ripple.
 reflexivity.

 (* The base is proven by "triv" as a more general version of this goal has already
     been proven *)
  simp'.
  triv.
Qed.

(********************************************************************************)
(* Automated generalisation examples                                            *)
(********************************************************************************)

(* Generalising the common subterms "rev x" and "rev y" *)
Goal forall (A:Type) (x y:list A),
  length (rev x ++ rev y) = length (rev x) + length (rev y).
intros; gen.
d'.
Qed.

(* Generalising apart "x" *)
Goal forall x y, (x * x) * y = x * (y * x).
intros; gen.
d.
Qed.

(* Generalisation apart "x" *)
Goal forall (A:Type) (x:list A), length (x ++ x) = length x + length x.
intros; gen.
d'.
Qed.

(********************************************************************************)
(* Testing tool                                                                 *)
(********************************************************************************)

(*

The testing tool searches for a counterexample to the current Coq goal by:

- (Generate) Simply typed "Set" variables are instantiated with randomly
   generated terms.

- (Test) A counterexample is found when all Prop assumptions are provable and the
  conclusion is not provable. When checking this, we only support propositions that
  make use of "=", "<>", "/\", "\/", "<", "<=", ">" and ">=", and propositions cannot
  contain quantifiers.

The proof automation makes use of this tool to identify overgeneralisations. The
testing tool is also useful in manual proofs.

Uncomment the "try" in each example below to see the counterexample found.
When a counterexample is found, an evaluation trace is shown.
*)

(* A non-theorem *)
Goal forall x, (x - 1) + 1 = x.
try qc.
(*
*** COUNTEREXAMPLE FOUND ***

Variable instantiations:
x := 0

Instantiated and simplified conclusion showing the contradiction:
(x - 1 + 1 = x)
(0 - 1 + 1 = 0)
(0 + 1 = 0)
(1 = 0)
*)
Admitted.

(* The counterexample above indicates a missing side-condition. The testing
tool can be used to check we have now written a theorem statement. *)
Goal forall x, x <> 0 -> (x - 1) + 1 = x.
qc.
intuition.
Qed.

Goal True.
(* Tells the testing tool to replace (A:Type) in goals with (A:nat) when testing *)
ReplaceInTests T nat.
Admitted.

Goal forall (T:Type) (x y:list T), rev (x ++ y) = rev x ++ rev y.
try qc.
(*
*** COUNTEREXAMPLE FOUND ***

Variable instantiations:
y := [0; 0]
x := [1]

Instantiated and simplified conclusion showing the contradiction:
(rev (x ++ y) = rev x ++ rev y)
(rev ([1] ++ [0; 0]) = rev [1] ++ rev [0; 0])
(rev [1; 0; 0] = [1] ++ [0; 0])
([0; 0; 1] = [1; 0; 0])
*)
Admitted.

Goal forall (T:Type) (x y:list T), rev (x ++ y) = rev y ++ rev x.
qc.
d'.
Qed.

Goal forall (T:Type)(a : btree T), postorder (mirror a) = rev (postorder a).
try qc.
(*
*** COUNTEREXAMPLE FOUND ***

Variable instantiations:
a := (node 1 (leaf 0) (leaf 0))

Instantiated and simplified conclusion showing the contradiction:
(postorder (mirror a) = rev (postorder a))
(postorder (mirror (node 1 (leaf 0) (leaf 0))) =
 rev (postorder (node 1 (leaf 0) (leaf 0))))
(postorder (node 1 (leaf 0) (leaf 0)) = rev [0; 0; 1])
([0; 0; 1] = [1; 0; 0])
*)
Admitted.

Goal forall (T:Type)(a : btree T), postorder (mirror a) = rev (preorder a).
qc.
d.
Qed.

Goal forall (S T:Type) (f:S -> T) (x y:list S),
  rev (map f (x ++ y)) = rev (map f x) ++ rev (map f y).
ReplaceInTests S nat.
ReplaceInTests T nat.
(* Randomly instantiate variables with type (nat -> nat) to "S" or "pred" *)
Generator (nat -> nat) [S; pred].
try qc.
(*
*** COUNTEREXAMPLE FOUND ***

Variable instantiations:
y := [1]
x := [0]
f := S

Instantiated and simplified conclusion showing the contradiction:
(rev (map f (x ++ y)) = rev (map f x) ++ rev (map f y))
(rev (map S ([0] ++ [1])) = rev (map S [0]) ++ rev (map S [1]))
(rev (map S [0; 1]) = rev [1] ++ rev [2])
(rev [1; 2] = [1] ++ [2])
([2; 1] = [1; 2])
*)
Admitted.

(*
Limitations:

- Term generation only works for simply typed inductive data types.

- Tests that involve large terms can crash Coq. For example, power and factorial
functions can generate large terms during testing.

- User-defined inductive predicates are not supported. For example, we cannot test
if "In 0 [0]" is provable. One workaround is to define a function that is equilavent
to the inductive predicate you want to use and use "setoid_rewrite" to rewrite the
latter to the former before testing.

- There are no support yet for writing custom term generators. This can
make it difficult to find counterexamples when the goal assumptions express
conditions that are hard to satisfy with random variable instantiations.
*)
