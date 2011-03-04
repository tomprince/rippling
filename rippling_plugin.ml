(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    /   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(*
Tactics for inductive proof automation including:
- rippling-based rewriting
- automated generalization
- Quickcheck-like testing tool

Written by Sean Wilson (sean.wilson@ed.ac.uk).
*)

(* Higher debug level means more verbose debugging output *)
let debug_level = 0
(* Output proof log trace files (log output can slow performance) *)
let debug_show_proof_log = false
(* Display pruned ripple steps such as when loops are detected. Useful to see when debugging and finding search redundancy *)
let show_pruned_ripple_step = false
(* When annotating a transition, all annotations found are shown along. *)
let display_all_transition_annotations = false

(* Instead of rippling, first try to solve the goal trivially, then try "simpl" followed by "fertilisation" *)
let try_simpl_fertilise = false
(* As long as any embedding are maintained, call "simpl" before calling rippling *)
let try_simpl_ripple = false

(* Put cached lemmas into rippling rule database *)
let use_cached_lemmas_while_rippling = true
(* Put identified simplification rules into simplification rule database *)
let cache_simplification_rules = true
(* Whether to cache proven theorems or not *)
let cache_lemmas = true

(* Cache lemmas for use with trivial/auto tactic*)
let cache_trivial_lemmas = true

(* Maximum number of steps that can be applied in one rippling proof *)
let max_ripple_depth = 10

(* Rippling lemma database containing only basic definitions *)
let ripple_basic_db = "ripple_basic"
(* Rippling lemma database containing cached lemmas *)
let ripple_cached_db = "ripple_cached"

let ripple_all_db = [ripple_basic_db; ripple_cached_db]

let trivial_db = "cache"

(* Amount to indent debug messages *)
let indent_level = ref 0

open List
open Printf
open Cctac
open Tactics
open Tacticals
open Hipattern
open Names
open Libnames
open Proof_type
open Tacticals
open Tacinterp
open Tactics
open Pp
open Util
open Univ
open Term
open Environ
open Extraargs
open Mod_subst
open Evd
open Libnames
open Coqlib
open Term
open Names
open Util
open Printer
open Clenv
open Clenvtac
open Nameops
open Sign
open Term
open Termops
open Declarations
open Inductive
open Inductiveops
open Reductionops
open Environ
open Libnames
open Tacred
open Tacmach

(* TODO: Make this configurable from coqide *)
let noninterp_default_side_conditions_tactic =
  (* "solve" prevents rewrites where the side-conditions cannot be solved. This is important as some side-conditions will be
     unprovable *)
  <:tactic<solve [simp; triv]>>
let default_side_conditions_tactic = interp noninterp_default_side_conditions_tactic

(* Hash table for constr terms *)
module ConstrMap =
  Hashtbl.Make
    (struct
      type t    = Term.constr
      let equal = eq_constr
      let hash  = Hashtbl.hash
    end)

exception No_embeddings
exception Already_seen
exception Not_reducing

let string_of_ppcmds p = Pp.pp_with Format.str_formatter p; Format.flush_str_formatter()

(* Returns the cartesian product of a and b storing the pairings as lists. *)
let rec cartp a b =
 match a with
   [] -> []
 | h::t -> (map (fun x -> h@x) b) @ (cartp t b)

(* Generates all the ways to pick one item each out of several lists of items e.g.
   input: [[1;2]; [3;4]] output: [[1; 3]; [1; 4]; [2; 3]; [2; 4]] *)
let cartp_multi x =
  if x = [] then [] else
  let y = map (fun a -> map (fun b -> [b]) a) x in
  fold_left cartp (hd y) (tl y)

(*****************************************************************************)
(* Taken from dev/top_printers.ml. Useful for seeing underlying              *)
(* representation of Coq term when developing tactics. *)

let cnt = ref 0

let cast_kind_display k =
  match k with
  | VMcast -> "VMcast"
  | DEFAULTcast -> "DEFAULTcast"

let constr_display csr =
  let rec term_display c = match kind_of_term c with
  | Rel n -> "Rel("^(string_of_int n)^")"
  | Meta n -> "Meta("^(string_of_int n)^")"
  | Var id -> "Var("^(string_of_id id)^")"
  | Sort s -> "Sort("^(sort_display s)^")"
  | Cast (c,k, t) ->
      "Cast("^(term_display c)^","^(cast_kind_display k)^","^(term_display t)^")"
  | Prod (na,t,c) ->
      "Prod("^(name_display na)^","^(term_display t)^","^(term_display c)^")\n"
  | Lambda (na,t,c) ->
      "Lambda("^(name_display na)^","^(term_display t)^","^(term_display c)^")\n"
  | LetIn (na,b,t,c) ->
      "LetIn("^(name_display na)^","^(term_display b)^","
      ^(term_display t)^","^(term_display c)^")"
  | App (c,l) -> "App("^(term_display c)^","^(array_display l)^")\n"
  | Evar (e,l) -> "Evar("^(string_of_int e)^","^(array_display l)^")"
  | Const c -> "Const("^(string_of_con c)^")"
  | Ind (sp,i) ->
      "MutInd("^(string_of_mind sp)^","^(string_of_int i)^")"
  | Construct ((sp,i),j) ->
      "MutConstruct(("^(string_of_mind sp)^","^(string_of_int i)^"),"
      ^(string_of_int j)^")"
  | Case (ci,p,c,bl) ->
      "MutCase(<abs>,"^(term_display p)^","^(term_display c)^","
      ^(array_display bl)^")"
  | Fix ((t,i),(lna,tl,bl)) ->
      "Fix(([|"^(Array.fold_right (fun x i -> (string_of_int x)^(if not(i="")
        then (";"^i) else "")) t "")^"|],"^(string_of_int i)^"),"
      ^(array_display tl)^",[|"
      ^(Array.fold_right (fun x i -> (name_display x)^(if not(i="")
        then (";"^i) else "")) lna "")^"|],"
      ^(array_display bl)^")"
  | CoFix(i,(lna,tl,bl)) ->
      "CoFix("^(string_of_int i)^"),"
      ^(array_display tl)^","
      ^(Array.fold_right (fun x i -> (name_display x)^(if not(i="")
        then (";"^i) else "")) lna "")^","
      ^(array_display bl)^")"

  and array_display v =
    "[|"^
    (Array.fold_right
       (fun x i -> (term_display x)^(if not(i="") then (";"^i) else ""))
       v "")^"|]"

  and sort_display = function
    | Prop(Pos) -> "Prop(Pos)"
    | Prop(Null) -> "Prop(Null)"
    | Type u ->
  incr cnt; pp (str "with " ++ int !cnt ++ pr_uni u ++ fnl ());
  "Type("^(string_of_int !cnt)^")"

  and name_display = function
    | Name id -> "Name("^(string_of_id id)^")"
    | Anonymous -> "Anonymous"

  in
    msg (str (term_display csr) ++fnl ())
open Format
 let print_pure_constr csr =
  let rec term_display c = match kind_of_term c with
  | Rel n -> print_string "#"; print_int n
  | Meta n -> print_string "Meta("; print_int n; print_string ")"
  | Var id -> print_string (string_of_id id)
  | Sort s -> sort_display s
  | Cast (c,_, t) -> open_hovbox 1;
      print_string "("; (term_display c); print_cut();
      print_string "::"; (term_display t); print_string ")"; close_box()
  | Prod (Name(id),t,c) ->
      open_hovbox 1;
      print_string"("; print_string (string_of_id id);
      print_string ":"; box_display t;
      print_string ")"; print_cut();
      box_display c; close_box()
  | Prod (Anonymous,t,c) ->
      print_string"("; box_display t; print_cut(); print_string "->";
      box_display c; print_string ")";
  | Lambda (na,t,c) ->
      print_string "["; name_display na;
      print_string ":"; box_display t; print_string "]";
      print_cut(); box_display c;
  | LetIn (na,b,t,c) ->
      print_string "["; name_display na; print_string "=";
      box_display b; print_cut();
      print_string ":"; box_display t; print_string "]";
      print_cut(); box_display c;
  | App (c,l) ->
      print_string "(";
      box_display c;
      Array.iter (fun x -> print_space (); box_display x) l;
      print_string ")"
  | Evar (e,l) -> print_string "Evar#"; print_int e; print_string "{";
      Array.iter (fun x -> print_space (); box_display x) l;
      print_string"}"
  | Const c -> print_string "Cons(";
      sp_con_display c;
      print_string ")"
  | Ind (sp,i) ->
      print_string "Ind(";
      sp_display sp;
      print_string ","; print_int i;
      print_string ")"
  | Construct ((sp,i),j) ->
      print_string "Constr(";
      sp_display sp;
      print_string ",";
      print_int i; print_string ","; print_int j; print_string ")"
  | Case (ci,p,c,bl) ->
      open_vbox 0;
      print_string "<"; box_display p; print_string ">";
      print_cut(); print_string "Case";
      print_space(); box_display c; print_space (); print_string "of";
      open_vbox 0;
      Array.iter (fun x ->  print_cut();  box_display x) bl;
      close_box();
      print_cut();
      print_string "end";
      close_box()
  | Fix ((t,i),(lna,tl,bl)) ->
      print_string "Fix("; print_int i; print_string ")";
      print_cut();
      open_vbox 0;
      let rec print_fix () =
        for k = 0 to (Array.length tl) - 1 do
    open_vbox 0;
    name_display lna.(k); print_string "/";
    print_int t.(k); print_cut(); print_string ":";
    box_display tl.(k) ; print_cut(); print_string ":=";
    box_display bl.(k); close_box ();
    print_cut()
        done
      in print_string"{"; print_fix(); print_string"}"
  | CoFix(i,(lna,tl,bl)) ->
      print_string "CoFix("; print_int i; print_string ")";
      print_cut();
      open_vbox 0;
      let rec print_fix () =
        for k = 0 to (Array.length tl) - 1 do
          open_vbox 1;
    name_display lna.(k);  print_cut(); print_string ":";
    box_display tl.(k) ; print_cut(); print_string ":=";
    box_display bl.(k); close_box ();
    print_cut();
        done
      in print_string"{"; print_fix (); print_string"}"

  and box_display c = open_hovbox 1; term_display c; close_box()

  and sort_display = function
    | Prop(Pos) -> print_string "Set"
    | Prop(Null) -> print_string "Prop"
    | Type u -> open_hbox();
  print_string "Type("; pp (pr_uni u); print_string ")"; close_box()

  and name_display = function
    | Name id -> print_string (string_of_id id)
    | Anonymous -> print_string "_"
  (* Remove the top names for library to avoid long names *)
  and sp_display sp =
(*    let dir,l = decode_kn sp in
    let ls =
      match List.rev (List.map string_of_id (repr_dirpath dir)) with
          ("Top"::l)-> l
  | ("Coq"::_::l) -> l
  | l             -> l
    in  List.iter (fun x -> print_string x; print_string ".") ls;*)
      print_string (string_of_mind sp)
  and sp_con_display sp =
(*    let dir,l = decode_kn sp in
    let ls =
      match List.rev (List.map string_of_id (repr_dirpath dir)) with
          ("Top"::l)-> l
  | ("Coq"::_::l) -> l
  | l             -> l
    in  List.iter (fun x -> print_string x; print_string ".") ls;*)
      print_string (string_of_con sp)

  in
    try
     box_display csr; print_flush()
    with e ->
  print_string (Printexc.to_string e);print_flush ();
  raise e
(*****************************************************************************)

(* Appends a string to itself n times *)
let rec padding str n = if n = 0 then "" else str ^ padding str (n - 1)

let debug_ignore level message =
  if level <= debug_level then
  (
    let m = str ("DBG" ^ (string_of_int level) ^ ": " ^ (padding " " !indent_level)) ++ message in
    pp (fnl() ++ m);

  (*Format.set_formatter_out_channel stdout;
    let string_of_ppcmds p = Pp.pp_with Format.str_formatter p; Format.flush_str_formatter() in
    let s = string_of_ppcmds m in
    printf "R%sR" s;*)
    flush_all()
  )
  else
    ()

let dmsg level message =
  debug_ignore level message

let dmsgs level message =
  debug_ignore level message

let dmsgc level message constr =
  debug_ignore level ((str message) ++ (str " = ") ++ Printer.pr_constr constr)

(* Displays ocaml representation of Coq term *)
let dmsgo level message constr =
  debug_ignore level ((str message) ++ (str " = "));
  if level <= debug_level then constr_display constr else ()

let msgconstr x y = msgnl (str x ++ str " = " ++ Printer.pr_constr y)
let msgconstro x y = msgnl (str x ++ str " = " ++ Printer.pr_constr y); y
let msgheading x = msgnl (str "\n##############  " ++ str x ++ str "  ##############")
let msgcurrentgoal gl = msgnl ((str "\n************** Current goal: ") ++ (pr_constr (pf_concl gl)))
let msgconstrlist c = map (fun f -> msgconstr "in list" f) c



(* case splits on match statements *)
let case_concl2 casesplit_tactic g=
    let term = (pf_concl g) in
(*     dmsgc 0 "case_concl term" term; *)
    let rec b =
      (fun r x ->
(*       dmsgc 0 "case_concl" x; *)
        match r with
        Some _ -> r
        | _    ->
              (*(match kind_of_term x with
                Case (_,_,case_term,_) -> dmsgc 0 "case_concl!!!" x
                | _ -> dmsgc 0 "no match" x)
                    ;*)
           match kind_of_term x with
                    (* Find the inner most case statement
                       Only allow closed terms e.g. "if c then ..." instead of "fun c => if c then ..." as case splitting will
                       fail on the latter *)
                    Case (_,_,case_term,_) when closed0 case_term -> Some case_term
                  | _ -> fold_constr b r x) in
      (*let found = fold_constr b None term in*)
      let found = b None term in

    match found with
      Some x ->
(*         Hiddentac.h_simplest_case x g *)
(*         let arg = valueIn (VConstr x) in (interp <:tactic<case_eq $arg; intros >>) g *)
        let arg = valueIn (VConstr ([],x)) in (casesplit_tactic arg g)
    | None -> tclFAIL 0 (str "No 'case' constructs found") g


(* Looks for a term of the form "match X..." in the conclusion and calls tactic "case X" if it finds one or fails *)
(* Case splits on innermost found *)
let case_concl g =
    let term = (pf_concl g) in
    let rec b =
      (fun r x ->
        match r with
        Some _ -> r
        | _    -> match kind_of_term x with
                    (* Find the inner most case statement (avoids information loss)
                       Only allow closed terms e.g. "if c then ..." instead of "fun c => if c then ..." as case splitting will
                       fail on the latter *)
                    Case (_,_,case_term,_) when closed0 case_term ->
                      (match fold_constr b r x with
                        Some x when closed0 x -> Some x
                       | _ -> Some case_term )
                  | _ -> fold_constr b r x) in
      (*let found = fold_constr b None term in*)
      let found = b None term in
    match found with
      Some x ->
        Hiddentac.h_simplest_case x g
   | None -> tclFAIL 0 (str "No 'case' constructs found") g

TACTIC EXTEND testtactic3224
| [ "case_concl" ] -> [ case_concl2 (fun arg -> (interp <:tactic<case_eq' $arg >>)) ]
END


(* FIXME: These references should be loaded from a theory file. Having trouble with module visability *)
let wave_out = ref (mkRel 1)
let wave_in = ref (mkRel 1)
let wave_hole = ref (mkRel 1)
let wave_sink = ref (mkRel 1)
let fertilise_rewrite = ref (mkRel 1)
let nat_type = ref (mkRel 1)
let natlist_type = ref (mkRel 1)

let contrib_name = "seanw"
let contrib_dir = [contrib_name]
let fix_sub_module = "FixSub"
let utils_module = "Utils"
let fixsub_module = contrib_dir @ [fix_sub_module]
let utils_module = contrib_dir @ [utils_module]
let init_constant dir s = gen_constant contrib_name dir s
let init_reference dir s = gen_reference contrib_name dir s

let fixsub = lazy (init_constant fixsub_module "Fix_sub")
let ex_pi1 = lazy (init_constant utils_module "ex_pi1")
let ex_pi2 = lazy (init_constant utils_module "ex_pi2")

let logic_dir = ["Coq";"Logic";"Decidable"]
let init_arith_modules = init_modules @ arith_modules
let coq_modules =
  init_arith_modules @ [logic_dir] @ zarith_base_modules
    @ [["Coq"]]

let init_arith_constant = gen_constant_in_modules "Seanw" init_arith_modules
let constant = gen_constant_in_modules "Seanw" coq_modules

let make_ref l s = lazy (init_reference l s)
let well_founded_ref = make_ref ["Init";"Wf"] "Well_founded"
let acc_ref = make_ref  ["Init";"Wf"] "Acc"
let acc_inv_ref = make_ref  ["Init";"Wf"] "Acc_inv"
let fix_sub_ref = make_ref ["subtac";"FixSub"] "Fix_sub"
let eq_ind = lazy (init_constant ["Init"; "Logic"] "eq")
let and_ind = lazy (init_constant ["Init"; "Logic"] "and")
let or_ind = lazy (init_constant ["Init"; "Logic"] "or")
let iff_ind = lazy (init_constant ["Init"; "Logic"] "iff")
let natind = lazy (init_constant ["Init"; "Datatypes"] "nat")
let coq_not = lazy (init_constant ["Init"; "Logic"] "not")
let coq_True = lazy (init_constant ["Init"; "Logic"] "True")
let coq_False = lazy (init_constant ["Init"; "Logic"] "False")
let gen_constant dir s = Coqlib.gen_constant "seanw" dir s
let eq_ind_r = lazy(gen_constant ["Init"; "Logic"] "eq_ind_r")
let plus_comm = lazy(gen_constant ["Arith"; "Plus"] "plus_comm")
let coq_eq_ind_r () = (constant "eq_ind_r")
let coq_proj1 = lazy (constant "proj1")
let coq_proj2 = lazy (constant "proj2")
let coq_sym_eq = lazy (constant "sym_eq")
let coq_le = lazy (constant "le")
let coq_lt = lazy (constant "lt")
let coq_ge = lazy (constant "ge")
let coq_gt = lazy (constant "gt")
let coq_0 = lazy (constant "O")
let coq_S = lazy (constant "S")

let get_fresh_theorem_name prefix =
  Namegen.next_global_ident_away (id_of_string prefix) (Pfedit.get_all_proof_names ())

let rec take n x =
  match n, x with
    0, x    -> []
  | n, []   -> raise Not_found
  | n, h::x -> h :: take (n-1) x

(* FIXME: Is a version of this not in refiner.mli somewhere? *)
let tclORELSESEQ = List.fold_left tclORELSE tclIDTAC

(* Returns all subterms of a term, not including curried versions *)
let collect_subterms2 c =
 let rec f r c =
  fold_constr f (c::r) c in
 fold_constr f [c] c

(* Returns all subterms of a term, including curried versions e.g. plus x is a subterm of plus x y
   FIXME: Refactor. Modified from w_unify_to_subterm in Unification module.  *)
let collect_subterms cl =
(* dmsgc 1 "startsubterm" cl; *)
  let iter_fail2 f a =
    let n = Array.length a in
    let rec ffail i =
      if i = n then []
      else
        (f a.(i))@(ffail (i+1))
    in ffail 0
  in
  let rec matchrec cl =
    let cl = strip_outer_cast cl in
    let m = (match kind_of_term cl with
    | App (f,args) ->
        let n = Array.length args in
        assert (n>0);
        let c1 = mkApp (f,Array.sub args 0 (n-1)) in
        let c2 = args.(n-1) in
        matchrec c1@matchrec c2
    | Case(_,_,c,lf) -> (* does not search in the predicate *)(matchrec c)@(iter_fail2 matchrec lf)
    | LetIn(_,c1,_,c2) ->  matchrec c1@ matchrec c2
    | Fix(_,(_,types,terms)) -> (iter_fail2 matchrec types)@(iter_fail2 matchrec terms)
    | CoFix(_,(_,types,terms)) -> (iter_fail2 matchrec types)@(iter_fail2 matchrec terms)
    | Prod (_,t,c) -> matchrec t@matchrec c
    | Lambda (_,t,c) -> matchrec t @matchrec c
    | _ -> [])
  in
    (try
       if closed0 cl
       then
       (
         (cl::m) (* subterm found *))
       else error "Bound 1"
     with _ ->
     m)
  in
 matchrec cl

(* True when a variable term occurs inside c *)
let occur_variable_term c =
  let rec occur_rec c =
    match kind_of_term c with
    | Const _ -> raise Occur
    | Var _ -> raise Occur
    | Rel _ -> raise Occur
    | _ -> iter_constr occur_rec c
  in
  (try occur_rec c; false with Occur -> true)

open List

(* Tries to revert all assumptions except for one. TODO: rewrite in ltac *)
let revert_except hyp g =
  match kind_of_term hyp with
  | Var id1 ->
    tclMAP
      (fun i -> match i with
        | (id,None,t) ->
        if (not (id = id1) &&
          not (is_Prop (pf_type_of g t)) && (* don't revert Prop variables like (x <> 0) as these mess up the inductive step assumtpion*)
          (occur_term (mkVar id) (pf_concl g) (* don't revert variables not mentioned in the conclusion as you get needless variables when you do induction *))
        ) then
          (* "try" needed as generalize will fail with dependent hypotheses e.g. when you generalize x=y without x and y *)
          tclTRY (tclTHEN (Hiddentac.h_generalize [mkVar id]) (clear [id]))
        else
          (fun g-> dmsg 6 (str "didn't revert");tclIDTAC g)
        | _ -> tclIDTAC)
    (pf_hyps g) g
  | _ -> tclIDTAC g

TACTIC EXTEND revert_except_tactic
[ "revert_except" constr(hyp) ] -> [ revert_except hyp ]
END

(* Returns LHS, RHS and clenv for an equation *)
let analyse_hypothesis gl c =
 let ctype = pf_type_of gl c in
 let eqclause  = Clenv.make_clenv_binding gl (c,ctype) Rawterm.NoBindings in
 let (equiv, args) = decompose_app (Clenv.clenv_type eqclause) in
 let rec split_last_two = function
   | [c1;c2] -> [],(c1, c2)
   | x::y::z ->
      let l,res = split_last_two (y::z) in x::l, res
      | _ -> raise Occur in
 let others,(c1,c2) = split_last_two args in
  eqclause,mkApp (equiv, Array.of_list others),c1,c2

(* FIXME: refactor analyse_hypothesis and analyse_hypothesis2 *)
let analyse_hypothesis2 gl c =
 let ctype = c in
 let eqclause  = Clenv.make_clenv_binding gl (c,ctype) Rawterm.NoBindings in
 let (equiv, args) = decompose_app (Clenv.clenv_type eqclause) in
 let rec split_last_two = function
   | [c1;c2] -> [],(c1, c2)
   | x::y::z ->
      let l,res = split_last_two (y::z) in x::l, res
      | _ ->raise Occur  in
 let others,(c1,c2) = split_last_two args in
  eqclause,mkApp (equiv, Array.of_list others),c1,c2

let get_sides_of_equation t g =
  let (_,_,lhs, rhs) = analyse_hypothesis2 g t in
  (lhs, rhs)

(* Logging code *****************************************)

(*
let logfile = ref (stderr)
let open_logfile name = (logfile := open_out ((Sys.getenv "HOME")^"/Temp/trace/" ^ name ^ ".xml"))
let log_write msg = Printf.fprintf (!logfile) "%s\n" msg
let close_logfile() = close_out (!logfile)
*)

(* Use this block instead to turn logging off *)
(* TODO: Need an easy way to turn off logging output *)
let logfile = ()
let open_logfile name = ()
let log_write msg = ()
let close_logfile() = ()
(*let open_logfile name = ()
let log_write msg = fprintf (!logfile) "%s\n" msg
let close_logfile() = ()*)

let indentmsg n s =
 let msg = s in dmsg 0 (msg);

  if debug_show_proof_log then
  (
    (* let msg = (str   (padding " " n)) ++ (s) in

    let b =  Buffer.create 1000000 in (* FIXME: Large buffer used otherwise messages are sometimes truncated. Not very effecient code *)
    Pp.msg_with (Format.formatter_of_buffer b) (msg++(str"\n"));
    Buffer.output_buffer (!logfile) b)
    *) (* TODO: Enable this to turn on trace logs *) ())

(* Returns true if tactic call has proven all goals *)
let all_goals_solved (g,_) = g.it = []

(* Calls tactic t and encloses its output inside XML tags (for giving proof search traces) *)
let tag_tactic2 msg params tact g =

  let tclORELSE0 t1 t2 g =
    let endtag = str ("</" ^ msg ^ ">") in

    let msgfail s e =

      indentmsg !indent_level (
        (if true (*s = str ""*) then (* FIXME: want to prune empty "msg" tags but comparision here gives "equal:functional value" exception*)
          (str "<fail/>")
        else
          (str "<fail msg=\"") ++ s ++ (str "\"/>"))
        ++ endtag);
        indent_level := !indent_level - 1;
      raise e in

    try
      indent_level := !indent_level + 1;
      indentmsg !indent_level ((str ("<"^msg^" ")) ++ params ++ (str ">"));
      tclTHENSEQ [(fun g->
        let t = tact g in
        (
        if all_goals_solved t then indentmsg !indent_level (str ("<success/>")));
        pp (endtag);
        indent_level := !indent_level - 1;
        t);
        (fun g -> (tclIDTAC g))] g
    with (* Breakpoint *)
   Refiner.FailError (_,s) as e ->
     msgfail (Lazy.force s) e
   | Stdpp.Exc_located (s', Refiner.FailError (lvl,s)) as e ->
     msgfail (Lazy.force s) e
   | e ->
     msgfail (str "") e
  in
    tclORELSE0 (tact) tclIDTAC g

let tag_tactic msg tact g =
  tag_tactic2 "tactic" (str ("name=\""^msg^"\"")) tact g

let tag_group msg tact g =
  tag_tactic2 "group" (str ("name=\""^msg^"\"")) tact g

let tag_tclTHENSEQ tactlist =
  let rec tag t =
  match t with
  | [] -> tclIDTAC
  | h::[] -> tclTHENSEQ[h ;
          (fun g ->
            (tag []) g)]
  | h::t -> tclTHENSEQ[h ;
          (fun g ->
            tag_tactic2 "goal" ((str "description=\"")++(pr_constr (pf_concl g))++(str "\""))
            (tag t) g)]
 in tag tactlist

let tag_tclORELSESEQ tactlist =
  let rec tag t =
  match t with
  | [] -> tclFAIL 0 (str "")
  | h::t -> tclORELSESEQ[
  (fun g->(tag_tactic2 "branch" (str "") h) g);
          (fun g -> (tag t) g)]
    in tag tactlist

let dummy_type = mkProp

(* A constant is 1) a variable or a constant applied to a constructor or 2) a constructor *)
let is_constant c =
  let rec is_constant' c =
    match kind_of_term c with
    App (f1, params) when isInd f1 || isConstruct f1 ->
      Array.iter
        (fun x -> try is_constant' x with Occur ->
           if not (isVar x) && not (isConst x) && not (isRel x) then raise Occur)
        params
   | Construct _ | Ind _ -> ()
   | _ -> raise Occur
  in
  try is_constant' c; true with Occur -> false

TACTIC EXTEND isconstant
| [ "is_constant" constr(c) ] -> [ if is_constant c then tclIDTAC else tclFAIL 0 (str "Not a constant.")]
END

(* Succeeds if c is a constructor *)
TACTIC EXTEND IsConstructor
| [ "is_constructor" constr(c) ] -> [ if isInd c || isConstruct c then tclIDTAC else tclFAIL 0 (str "Not a constructor.")]
END

(* Taken from contrib/funind/merge.ml *)
(** Operations on names and identifiers *)
let id_of_name = function
    Anonymous -> id_of_string "H"
  | Name id   -> id;;
let name_of_string str = Name (id_of_string str)
let string_of_name nme = string_of_id (id_of_name nme)

let is_evaluable c = try match global_of_constr c with VarRef _ | ConstRef _ -> true | _ -> false with _ -> false

let evaluable_of_constr c =
  let r = global_of_constr c in
  match r with
         | ConstRef c -> EvalConstRef c
         | VarRef c -> EvalVarRef c
         | _ ->
           errorlabstrm "evaluable_of_constr"
            (str "Cannot coerce" ++ spc () ++ pr_global r ++ spc () ++
             str "to an evaluable reference")

(* Returns contents of first wave hole found inside term *)
let find_hole c =
 let rec f r c =
  (match kind_of_term c with
    App (c,al) when c = !wave_hole -> Some al.(1)
  | _ -> fold_constr f r c) in
(*  match fold_constr f None c with Some x -> x | None -> raise Not_found *)
 fold_constr f None c

(* Returns contents of first wave sink found inside term *)
let find_sink c =
 let rec f r c =
  (match kind_of_term c with
    App (c,al) when c = !wave_sink -> Some al.(1)
  | _ -> fold_constr f r c) in
 match fold_constr f None c with Some x -> x | None -> raise Not_found

let has_sink c = try (ignore (find_sink c); true) with _ -> false

(* Removes all the differences and annotations from an annotated term *)
let rec remove_differences annotated =
  match kind_of_term annotated with
  | App (c,al) when c = !wave_hole or c = !wave_sink -> remove_differences al.(1)
  | App (c,al) when c = !wave_out or c = !wave_in ->
    (match find_hole al.(1) with Some hole -> remove_differences hole | None -> anomaly "Hole expected in wave front.")
  | _ -> map_constr remove_differences annotated

(* Removes all the annotation functions from an annotated term *)
let rec remove_annotations annotated =
  match kind_of_term annotated with
  | App (c,al) when c = !wave_hole or c = !wave_sink or c = !wave_out or c = !wave_in -> remove_annotations al.(1)
  | _ -> map_constr remove_annotations annotated

(* Finds all the ways a skeleton term can be embedded into an erasure term *)
let rec annotate2 eq inside_diff erasure skeleton g =
(* dmsgc 0 "erasure" erasure; *)
(* dmsgc 0 "skeleton" skeleton; *)
(*   print_pure_constr erasure; *)
(*   print_pure_constr skeleton; *)
  let mkannotated_term annotation term =
    (* Add typing to annotated terms. This is needed so we can compare annotated terms from the user
    (e.g. for unit tests), which will contain correct typing, without having to alter either term first *)
    (* If the erasure contains a meta-variable not declared in g (e.g. if we are trying to annotate
    terms that are not in the goal), pf_type_of will throw an exception when getting the type of this
    meta-variable so a dummy type is used. *)
    let term_type = try (pf_type_of g term) with _ -> dummy_type in
    mkApp (annotation, [|term_type; term|]) in

  let mkwaveout t = mkannotated_term !wave_out t in
  let mkwavehole t = mkannotated_term !wave_hole t in
  (*let mkwavesink t = mkannotated_term !wave_sink t in*)
  let mkwavein t = mkannotated_term !wave_in t in

  (*   dmsg 0 (str "matching " ++ pr_constr erasure ++ str " " ++ pr_constr skeleton); *)
  if eq erasure skeleton then
    ((*     dmsg 0 (str "equal"); *) if inside_diff then [mkwavehole skeleton] else [erasure])
  (* ?1 should not e,g. matches againsts (?1 + x) *)
  else if isMeta skeleton && not (occur_term skeleton erasure) then
    (* Trick: Storing the metavariable as the sink type so we can tell which metavariable matched to which term *)
    [mkApp (!wave_sink, [|skeleton; erasure|])]
  else
    match kind_of_term erasure with
    | App (ef1, ea1) ->
    (
      (* When the head term of an erasure and a skeleton are the same e.g. s:= plus x y e:= plus (S S x) (S S y),
         find ways that the skeleton parameters can match within the corresponding erasure parameters *)
      let appmatch =
        (match kind_of_term skeleton with
        | App (ef2, sa1) when eq ef1 ef2 && Array.length ea1 = Array.length sa1 ->
           (* Each skeleton parameter must embed into an erasure parmater in same position *)
           (try
              (* nth list item gives list of ways to annotate erasure parameter n with skeleton parameter n*)
              let params =
                Array.mapi (fun i param ->
                  let a = (annotate2 eq false param sa1.(i) g) in
                  if a = [] then raise No_embeddings else a) ea1 in
              (* Generate every way of choosing a set of annotated parameters to build an annotated app term *)
              let annotated_params_sets = cartp_multi (Array.to_list params) in
              let hole a = if inside_diff then [mkwavehole a] else [a] in
              flatten (List.map (fun f-> hole (mkApp (ef2, Array.of_list f))) annotated_params_sets)
            with _ -> [])
        | _ -> []) in

        (* Find ways in which the whole skeleton can be matched inside just one parameter of the erasure *)
        let rec annotate_parameters =
          (* Returns copy of app term with parameter i replaced with annotated version *)
          let annotate_one_param annotated index =
              (* Arrays mutable so we need to copy old parameters before annotating them. *)
              let updated_params = Array.copy ea1 in
              updated_params.(index) <- annotated;
              let a = mkApp(ef1, updated_params) in
              if inside_diff then [a] else [mkwaveout a] @ (if has_sink a then [mkwavein a] else [])(*sink restriction *)
          in

          (* Generate all final annotation permutations for each parameter *)
          let am = Array.mapi (fun i param ->
             let a = annotate2 eq true ea1.(i) skeleton g in
             if a <> [] then
               List.map (fun annotation -> annotate_one_param annotation i) a
             else
               [])
             ea1 in
          flatten(flatten(Array.to_list am))
       in
      appmatch @ annotate_parameters
    )
    | _ -> (*dmsg 0 (str "no match");*) (* no match *) []

let annotate erasure skeleton g =
(* dmsgc 0 "erasure" erasure;dmsgc 0 "skeleton" skeleton; *)

  (* Annotation sinks are OK if each metavariable with the same id in the skeleton embeds against the same term in the erasure e.g.
     (forall n, f n n) embeds into (f 1 1) but not (f 1 2) *)
  (*let sinks_ok a =
    let rec get acc c =
      (match kind_of_term c with
         (* The sink type stores the metavariable name *)
         App (c, [|meta; term|]) when c = !wave_sink ->
          let i = destMeta meta in
          (try
            let sink_contents = assoc i acc in
            (* This sink has been seen already so check it contains the same term as before *)
            if eq_constr sink_contents term then fold_constr get acc c else raise Occur
          with Not_found ->
            (* Store metavariable and matched term and continue traversing *)
            fold_constr get ((i, term)::acc) term)
      | _ -> fold_constr get acc c) in
    try get [] a; true with Occur -> false in*)

  (* Replace universally quantified variables in skelteon with metavariables *)
  let skeleton2 = (Clenv.make_clenv_binding g (skeleton,skeleton) Rawterm.NoBindings).templtyp.rebus in
  (* Generate annotations *)
  let annotations = annotate2 eq_constr false erasure skeleton2 g in

  (* Sinks can be allowed to differ to allow weak fertilisation *)
  (*let annotations = filter sinks_ok annotations in*)

  (* Annotated term minus differences should equal skeleton *)
  (*let skeleton_annotated a =
    let r = remove_differences a in
    dmsgc 0 "a" a; dmsgc 0 "r" r; dmsgc 0 "skeleton2" skeleton2;
    (* FIXME: Will not work for comparing ?1 = 0 (i.e. sinks) with x = 0. Must check for unification instead *)
    assert (eq_constr r skeleton2)
  in
  iter skeleton_annotated annotations;*)

  (* Annotated term minus annotations should equal the erasure *)
(*  let erasure_unaltered a =
    let r = remove_annotations a in
    (*dmsgc 0 "a" a; dmsgc 0 "r" r; dmsgc 0 "erasure" erasure;*)
    assert (eq_constr r erasure)
  in
  iter erasure_unaltered annotations;*)

  annotations

type 'a tree =
   Empty
 | Node of 'a * ('a tree list)

type tree_annotation = Skel | Sink | WaveIn of int | WaveOut of int

let rec depth t =
  match t with
  | Empty -> 0
  | Node (_,t2) -> 1 + List.fold_left max 0 (List.map (fun t -> depth t) t2)

let rec string_of_tree t =
  match t with
   Empty -> ""
  | Node (a,b) -> "("^(string_of_int a)^" ["^(String.concat ",\n" (map string_of_tree b))^"])"

(* Generates rippling measure tree from term. *)
let rec measure_tree wave_dir (c : constr) =
  let f x = Node(Skel, ((Array.fold_left (fun r al -> (measure_tree wave_dir al)::r) [] x))) in
  match kind_of_term c with
  | App (c,al) when c = !wave_hole -> anomaly "measure_tree: hole unexpectedly found outside of wave front."
  | App (c,al) when c = !wave_in || c = !wave_out ->
    (* Create measure tree of the hole inside this wave front. Note: hole could contain other wave fronts/holes *)
    (* Returns the first term found inside a hole and the size of the wave front it was found in. *)
    let find_hole c =
      let result = ref (0, None) in
      let rec f size term =
        match kind_of_term term with
          App (c,al) when c = !wave_hole -> result := (size, Some al.(1));raise Occur
        | _ -> iter_constr (f (size+1)) term
      in ((try f 0 c  with Occur -> ()); !result)
    in

    let (wavefront_size,hole_term) = find_hole al.(1) in
      (match hole_term with
        None -> anomaly "measure_tree: hole not found inside wave front."
      | Some h ->
      if wavefront_size = 0 then (dmsgc 0 "oops!" al.(1));
        let m = measure_tree wave_dir h in

        if wave_dir = c then
          (* Modify hole tree to reflect that it has 1 wave front around the root term. The size of the wave front
            is important as wave fronts getting smaller represents progress *)
          (match m with
            Empty -> anomaly "measure_tree: hole unexpectedly returned empty measure tree."
          | Node (_,t) ->
                Node((if wave_dir = !wave_out then WaveOut wavefront_size else WaveIn wavefront_size ), t)
          )
        else (* this wave front is being ignored *)
          m
      )
  | App (c,al) when c = !wave_sink -> Node(Sink, [])
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _ | Construct _) -> Node(Skel, [])
  | Cast (c,k,t) -> f [|c; t|]
  | Prod (na,t,c) -> f [|t; c|]
  | Lambda (na,t,c) -> f [|t; c|]
  | LetIn (na,b,t,c) -> f [|b; t; c|]
  | App (c,al) -> f al
  | Evar (e,l) -> f l
  | Case (ci,p,c,bl) -> f (Array.append [|p; c|] bl)
  | Fix (ln,(lna,tl,bl)) -> f (Array.append tl bl)
  | CoFix(ln,(lna,tl,bl)) -> f (Array.append tl bl)

let is_annotation_app a =
  a = !wave_out || a = !wave_in || a = !wave_sink || a = !wave_hole

(* Calculate dsum measure from ripple measure tree *)
let dsum_measure c =
  let closest_sink_distance t =
    let sofar : int option ref = ref None in
    let rec closest_sink_distance' t depth =
    match t with
      Empty -> ()
    | Node (v,t2) ->
      ((match v with
      | Sink -> sofar := Some (match !sofar with None -> depth | Some p -> min depth p)
      | _ -> List.iter (fun t -> closest_sink_distance' t (depth + 1)) t2))
    in
    closest_sink_distance' t 0;
    match !sofar with None -> (*inward front without a sink*) 0 | Some p -> p
  in

  (* Whether to count an n height wave front as n wave fronts *)
  let count_compound_wave_fronts = false in

  let measure = ref 0 in
  let rec traverse t depth =
    match t with
      Empty -> ()
    | Node (v,t2) ->
      ((match v with
       | WaveOut s ->
         measure := !measure + depth * (if count_compound_wave_fronts then s  else 1)
       | WaveIn s -> measure := !measure + (closest_sink_distance t) * (if count_compound_wave_fronts then s  else 1)
      | _ -> ());
       List.iter (fun t -> traverse t (depth + 1)) t2)
    in
   let wo = measure_tree !wave_out c in
    let wi = measure_tree !wave_in c in
   traverse wo 0;
   traverse wi 0;
  !measure

(* Calculate list-based ripple measure *)
let measure_list c =
  let measure_list2 t =
    let a = Array.make (depth t) 0 in
    let rec traverse t depth =
      match t with
        Empty -> ()
      | Node (v,t2) ->(match v with WaveIn s | WaveOut s -> a.(depth) <- (a.(depth) + s) | _ -> ());
                      List.iter (fun t -> traverse t (depth + 1)) t2
      in traverse t 0; (Array.to_list a) in

  let out_tree = measure_tree !wave_out c in
  let out_list = (measure_list2 out_tree) in

  let in_tree = measure_tree !wave_in c in
  let in_list = measure_list2 in_tree in

  let mlist = (rev out_list) @ in_list in
  mlist

let rec lexicographic_compare left right =
  match left, right with
      lh::lt, rh::rt ->
       (if      lh = rh then lexicographic_compare lt rt
        else if (lh<rh) then -1
        else                  1)
    | [], [] -> 0
    | _ -> error ("Measure lists are meant to be the same length. Is difference matching working?")

(* does going from left to right make progress? *)
let rec measure_list_decreasing left right =
  lexicographic_compare right left < 0

let rec measure_list_increasing left right =
  lexicographic_compare right left > 0

(* Does given embed into the goal? *)
let embeds given goal g = annotate goal given g <> []

(* Does given embed into term with differences? *)
let embeds_with_differences given goal g =
  let a = annotate goal given g in
  if a = [] then false else (if length a = 1 then false else true)

(* Returns true if the ripple measure for several givens decreases. At least one given must reduce its measure
  and no givens can increase their measure *)
let rec measures_decreasing (left, right) =
  measure_list_decreasing (List.concat left) (List.concat right)

assert (lexicographic_compare [0;2;0;0] [0;1;2;0] = 1);;
assert (lexicographic_compare [0;1] [0;1] = 0);;
assert (lexicographic_compare [1;0] [0;1] = 1);;
assert (lexicographic_compare [0;1] [1;0] = -1);;
assert (lexicographic_compare [0;1;0] [0;0;1] = 1);;
assert (lexicographic_compare [0;0;1] [0;1;0] = -1);;

assert (measure_list_decreasing [1;0] [0;1]);;
assert (measure_list_decreasing [1;0;0] [0;1;0]);;
assert (measure_list_decreasing [1;0;0] [0;0;1]);;
assert (measure_list_decreasing [0;1;0] [0;0;1]);;
assert (measure_list_decreasing [2;0;0] [1;0;0]);;
assert (measure_list_decreasing [0;2;0] [0;1;0]);;
assert (measure_list_decreasing [2;0;0] [1;1;0]);;
assert (measure_list_decreasing [0;1;1;0] [0;0;2;0]);;

assert (measure_list_increasing [2;0;0] [2;1;0]);;
assert (measure_list_increasing [0;0;0;2;0] [0;0;1;1;0]);;

let measure_list_to_string m =
  fold_left (fun x y -> x ^ (string_of_int y)) "" m

let measure_progress skel left right g=
  (*FIXME: only taking the first annotation *)
  dmsgc 3 "left" left;
  dmsgc 3 "right" right;
  dmsgc 3 "skel" skel;
  let lefta = annotate left skel g in
  let righta = annotate right skel g in
  dmsgc 3 "lefta" (hd (lefta));
  dmsgc 3 "righta" (hd (righta));
  let leftm = measure_list (hd(lefta)) in
  let rightm = measure_list (hd(righta)) in
  dmsg 3 (str ("leftm is "^ (measure_list_to_string leftm)));
  dmsg 3 (str ("\nrightm is " ^ (measure_list_to_string rightm)));
  measure_list_decreasing leftm rightm

(* Module for representing ripple measures TODO: Needs to be integrated into the rippling code so we can easily switch which measure
   is being used *)
module type MeasureType =
sig
 type measure
 val calculate_measure : constr -> measure
 val measure_decreasing : measure -> measure -> bool
 val measure_of_string : measure -> string
end

module ListMeasure : MeasureType =
struct
  type measure = int list
  let calculate_measure = measure_list
  let measure_decreasing = measure_list_decreasing
  let measure_of_string = measure_list_to_string
end

module DSumMeasure : MeasureType =
struct
  type measure = int
  let calculate_measure = dsum_measure
  let measure_decreasing = (<)
  let measure_of_string = string_of_int
end

module Measure = ListMeasure

let rec remove_duplicates eq =
  function
    [] -> []
  | h:: t ->
    if List.exists (eq h) t
    then remove_duplicates eq t
    else h::(remove_duplicates eq t)

(* Removes duplicate constrs in constr list *)
let rec removeconstrdups = remove_duplicates eq_constr

(*****
Code for a tactic that gives similar behaviour to the new "rewrite X at n" tactic. The use of the fomer should really
be replaced with the use of the latter in the future.
*****)

let unification_rewrite rewriterule_lhs c2 cl term_to_rewrite gl =
  dmsgc 3 "rewriterule_lhs" rewriterule_lhs;
  dmsgc 3 "term_to_rewrite" term_to_rewrite;

  let subterms = collect_subterms2 term_to_rewrite in
  let subterms = removeconstrdups subterms in

  let found =
  fold_left
    (fun r x ->
    try
      ((Unification.w_unify true (pf_env gl) Reduction.CUMUL ~flags:Unification.default_no_delta_unify_flags rewriterule_lhs x cl.evd), x)::r
    with _ -> r)
    [] subterms in

  let rec removedups =
    function
     ([]) -> []
   | (h:: t) ->
         if List.exists (compose (eq_constr (snd h)) snd ) t
      then removedups t
      else ((*dmsgc 1 "THIS WAS UNIFIED" (snd h);*)h::(removedups t))
 in
 let found = removedups found in

 (map (fun x -> let (evd',inital_term) = x in
 (* msgnl (pr_evar_defs evd'); *)

  let unified_rewrite_function = {cl with evd = evd' } in
  let rewritten_term = Clenv.clenv_nf_meta unified_rewrite_function c2 in
  (* dmsgc 1 "inital_term" unified_rewrite_function; *)
  (*  dmsgc 1 "inital_term" inital_term;  *)
  (*   dmsgc 6 "rewritten_term" rewritten_term; *)
  (*  dmsgc 6 "unified_rewrite_function" (Clenv.clenv_value unified_rewrite_function); *)
  evd',Clenv.clenv_value unified_rewrite_function, inital_term, rewritten_term)
  found)

let gen_rewrite_term lft2rgt lhs rewriterule rhs gl =
(* msgconstr "lhs" lhs;msgconstr "rhs" rhs; *)
  (* FIXME: the unification part for finding rewrite rule is broken in that it finds many lhs=>rhs that are the same. This is a hack to filter these rewrites. *)
  if (lhs = rhs) then [] else

  (*  let th = coq_eq_ind_r() in*)
  let goal = pf_concl gl in
  (*let new_but = Termops.replace_term lhs rhs goal in*)

  (* FIXME: ineffecient as this will do n+1 substitute traversals for n occurances *)
  let rec collect_subst n =
    ((*msgheading (string_of_int n);*)
    try (let t = (subst_term_occ (true,[n])(* replace only at n *) lhs goal) in
      t::(collect_subst (n+1)))
    with _ -> [])
  in
  let all_subst = collect_subst 1 in
    map (fun subst_term ->
    (* Abstract out the subterm to be rewritten *)
    let subst_fun = mkLambda (Anonymous, pf_type_of gl lhs, subst_term) in

    let subst_type = pf_type_of gl lhs in
    let rewriterule_term =
      if lft2rgt then
        rewriterule
      else
        (* use symmetry rule to change  rewrite direction to right to left*)
        mkApp(Lazy.force coq_sym_eq, [|subst_type;rhs;lhs;rewriterule|]) in

    (* The refine tactic term that does the rewriting *)
    let refine_term = (mkApp (coq_eq_ind_r(),
      [|subst_type;rhs; subst_fun;Evarutil.mk_new_meta(); lhs;rewriterule_term|])) in
    dmsgc 5 "refine_term" refine_term;
    refine_term)
  all_subst

let relation_rewrite c1 c2 (lft2rgt,cl) (*~new_goals *)gl =
  (dmsgs 3 ((str "Considering rule ")++((pr_constr c1)) ++ (str " => ") ++ ((pr_constr c2))));
  let rewrites = unification_rewrite c1 c2 cl (pf_concl gl) gl in
  let all = flatten (map (fun (sigma,cl,c1,c2) -> gen_rewrite_term lft2rgt c1 cl c2 gl) rewrites) in
  (*   iter (fun n -> dmsgc 1 "(*Rewrite found*): " n) all; *)
  if length all = 0 then
    (dmsg 4 (str "No rewrites found for this rule"); [])
  else
    (let refinelist = map (fun n -> (*refine *)refine_no_check n) all in refinelist)

let all_rewrites lft2rgt c (*~new_goals *)gl =
  let eqclause,_,c1,c2 = analyse_hypothesis gl c in
    if lft2rgt then
    relation_rewrite c1 c2 (lft2rgt,eqclause) gl
  else
    relation_rewrite c2 c1 (lft2rgt,eqclause) gl

(* Returns tactic to rewrite conclusion at position n. n = 1 is the first matching position from left to right,
   n = -1 is the first matching position from right to left *)
let rewrite_at rewrite orient position g =
  let r = all_rewrites orient rewrite g in
  let n = if position < 0 then
            (length r) + position
          else
            (position - 1) in
  if (n < 0 || n >= (length r)) then
    tclFAIL 0 (str ("rewrite_at: " ^ (string_of_int n) ^ " is not a valid matching position")) g
  else
    (nth r n) g

(****************)
let my_occur_var id c =
        let rec occur_rec c =
                match kind_of_term c with
                | Var i -> if id == i then raise Occur
                | _ -> iter_constr occur_rec c
  in
  try occur_rec c; false with
  Occur -> true


let occur_id id c =
        (my_occur_var id c) || not (noccurn 1 c)


(*
Implements the delayed generalisation algorithm to remove superflous assumptions from a cached lemma
*)
let rec remove_unused_lambdas r ty =
  (* dmsgc 0 "r" r; constr_display r; dmsgc 0 "t" t; constr_display t;*)
  match kind_of_term r with
  | Lambda (name,t,c) ->
    (match kind_of_term ty with
    | Prod (pa,pb,pc) ->
    (match name with
        Name id ->
          (* Check if the lambda term is used. As the lambda term variable could be referred
          to with Rel, we cannot just check for Var id terms. *)
          let (c,pc) = remove_unused_lambdas c pc in
          let lambda_used = occur_id id c in
          let lambda_usedp = occur_id id pc in
          (if lambda_used || lambda_usedp then
            (* Keep this lambda term *)
            (mkLambda (name, t, c), mkProd (pa,pb,pc))
          else
            (* Remove this lambda term. *)
            ((lift (-1) c), (lift (-1) pc)))
      | Anonymous ->
        (* FIXME: Need to check if anonymous variables are used too *)
        remove_unused_lambdas c pc
    )
    | _ -> (dmsg 0 (str "unexpected term structure!"); constr_display ty;(r,ty)))
  | _ ->  (r,ty)

(* Adds a cached lemma to suitable lemma databases *)
let auto_add_hint id base g =
   let lemma_type = pf_type_of g (Constrintern.global_reference id) in

  let add_rippling_rule orient =
    (match base with
    | Some bname ->
      Autorewrite.add_rew_rules bname [(Util.dummy_loc, Constrintern.global_reference id, orient, Tacexpr.TacId [])]
    | _ -> ()) in

  let add_hints_iff l2r lc n bl =
    Auto.add_hints true bl (Auto.HintsResolveEntry (List.map (fun x -> (n, l2r, x)) lc)) in

  if cache_trivial_lemmas then
    (let priority = Some 0 (* "trivial" will only use priority 0 rules *) in
    add_hints_iff false [(Constrintern.global_reference id)] priority [trivial_db]);

  (* Adds equation as L2R/R2L simplification rule *)
  let add_simplification_rule orient =
    if cache_simplification_rules then
      Autorewrite.add_rew_rules "simp" [(Util.dummy_loc, Constrintern.global_reference id, orient,
      (* use default side-condition tactic to solve any side-conditions this rule generates *)
      (* TODO: makes this a parameter of autorewrite instead for use with all rules *)
      noninterp_default_side_conditions_tactic
      (*Tacexpr.TacId []*)
      )]
  in

  (* Adds equation if it it is a simplification rule *)
  let is_simplification_rule equation =

    (* Get equation part of rule that would be used for rewriting with by seperating it from Prod terms *)
    let (prods, e) = decompose_prod equation in
    let (f, p) = destApp e in

    (* TODO: Use ltac for these checks *)
    (* Rule must be an equation *)
    (if eq_constr (Lazy.force eq_ind) f then
      (* Get LHS and RHS of equation *)
      (match p with [| _; lhs; rhs|] ->

      (* Check if equation has side-conditions *)
      let eqclause  = Clenv.make_clenv_binding g ((*optimised_term*)lemma_type,lemma_type) Rawterm.NoBindings in
      (* This check appears to find if instantiating the equation alone will leave any
         uninstantitated meta-variables in the rule (i.e. side-conditions) *)
      let has_side_conditions = clenv_independent eqclause <> [] in

      let allow_side_conditions = true in

      if (not (eq_constr lhs rhs)) && (allow_side_conditions || (not has_side_conditions)) then
      (
        (* using annotate2 instead of annotate because skeleton already has Prods replaced with meta variables at this point *)
        let embeds x y g = annotate2 eq_constr false x y g <> [] in
        (* If x embeds into y and is not equal, x must be simpler than y*)
        let embeds_lhs = embeds lhs rhs g in
        let embeds_rhs = embeds rhs lhs g in

        (* Determine if LHS/RHS of equation is a constant *)
        (* It's easier to check this with Ltac but Ltac needs a goal to operate on. To get around this, we just
           create a temporary subgoal that is processed by Ltac *)
        let constant_lhs = ref false in
        let constant_rhs = ref false in
        let arg = valueIn (VConstr ([],lemma_type)) in
        ignore (tclTHENSEQ [
          (interp <:tactic< let x := $arg in assert x; clear; intros >>);
          tclTRY (tclTHEN (interp <:tactic< constant_lhs >>) (fun g -> constant_lhs := true; tclIDTAC g));
          tclTRY (tclTHEN (interp <:tactic< constant_rhs >>) (fun g -> constant_rhs := true; tclIDTAC g))] g);

        let constant_lhs = !constant_lhs in
        let constant_rhs = !constant_rhs in

        if embeds_lhs then
          (dmsgc 0 ("Adding l2r simplification rule (embeds)") equation; add_simplification_rule true)
        else if embeds_rhs then
          (dmsgc 0 ("Adding r2l simplification rule (embeds)") equation; add_simplification_rule false)
        (* Do not want to add rules where both sides are constants as this could cause looping if added in both directions *)
        else if not constant_lhs && constant_rhs then
          (dmsgc 0 ("Adding l2r simplification rule (constant)") equation; add_simplification_rule true)
        else if constant_lhs && not constant_rhs then
          (dmsgc 0 ("Adding r2l simplification rule (constant)") equation; add_simplification_rule false);

        (* X => Y should be used as a rippling rule as long as X does not embed into Y
           e.g. n => n + 0 is not a productive rippling rule *)
        (* Ignore rules where X is a constant as these rules are rarely productive e.g. 0 => length []*)
        if not embeds_rhs && not constant_lhs then (dmsgc 0 ("Adding l2r rippling rule ") equation; add_rippling_rule true);
        if not embeds_lhs && not constant_rhs then (dmsgc 0 ("Adding r2l rippling rule ") equation; add_rippling_rule false)
      )
      | _ -> ()
      ))
    in
  is_simplification_rule lemma_type

(* Stores the proof for g as name in base if the tactic proves g *)
(* TODO: don't cache if the lemma exists already *)
let lemma_cache ?(add_as_hint=true) prefix solving_tactic base g =
  let name = get_fresh_theorem_name (prefix ^ "_temp") in
  (* If we can evaluate t, we know the lemma has been solved and cached *)
  let t = tclABSTRACT (Some name) solving_tactic g in
  ignore(t); (* keeping this for if we want to add an option to not optimise proofs *)

  (* Get the proof term and type of the cached lemma *)
  let cached_constant = (Constrintern.global_reference (name)) in
  let cached_type = pf_type_of g cached_constant in
  let cached_term = Indfun_common.def_of_const cached_constant in

  (* Use delayed generalisation algorithm on proof term  *)
  let (optimised_term,optimised_type) = remove_unused_lambdas cached_term cached_type in

(*   msgnl (str ("Discovered type: " ^ (string_of_id name) ^ ": ")++ Printer.pr_constr (cached_type)); *)
(*   msgnl (str ("Optimised term:        " ^ ": ")++ Printer.pr_constr (optimised_term)); *)
(*   msgnl (str ("Discovered opt : " ^ (string_of_id name) ^ ": ")++ Printer.pr_constr (optimised_type)); *)

  (* Add the optimised proof term as a new definition *)
  let save_theorem prefix theorem_type theorem_term =
    let id = get_fresh_theorem_name prefix in
    dmsg 0 (str ("Cached lemma " ^ (string_of_id id) ^ " : ") ++ pr_constr (theorem_type));
    let ce =
      { Entries.const_entry_body = theorem_term;
        const_entry_type = Some theorem_type;
        const_entry_opaque = false;
        const_entry_boxed = Flags.boxed_definitions()}
    in
    ignore (Declare.declare_constant id (Entries.DefinitionEntry ce, Decl_kinds.IsDefinition (Decl_kinds.Scheme)));
    id in

  let id = save_theorem prefix optimised_type optimised_term in

  if add_as_hint then auto_add_hint id base g;

  (* Solve this subgoal using the optimised proof o. It is important to not use the unoptimised proof term as the latter
  may use superflous assumptions, which then makes it impossible for these to be removed from the top-level cached lemma *)
  apply (Constrintern.global_reference (id)) g

let is_measure_reducing skel left g =
  try
    (if (measure_progress skel left (pf_concl g) g) then
      (dmsg 3 (str "Measure reducing!");tclIDTAC g)
    else
      (dmsg 3 (str "NOT measure reducing!"); tclFAIL 0 (str "Not measure reducing") g))
   with _ ->
     tclFAIL 0 (str "No annotations found?") g

let is_rippling_finished skel g =
  (*FIXME: only taking the first annotation *)
  let lefta = annotate (pf_concl g) skel g in
  if (lefta = []) then (dmsg 1 (str "is_rippling_finished called with no embedding!");msgconstr "goal" (pf_concl g); msgconstr "skel" skel) else ();
  let leftm = measure_list (hd(lefta)) in
  let rec fin m =
    match m with
      h::[] -> true (* h=1 is the only case? *)
    | h::t -> (h = 0 && fin t)
    | [] ->true
  in
  dmsgc 3 "Rippling finishing?" (hd lefta);
  dmsg 3 (str (string_of_bool (fin leftm)));
  fin leftm

let tclPRINTGOAL m g =
  dmsgs 0 ((str m) ++ (pr_constr (pf_concl g)));
  tclIDTAC g

(* Counts number of wave holes in an annotated term *)
  let num_wave_holes c =
    let rec f r c =
      (match kind_of_term c with
      App (c,al) when c = !wave_hole -> 1 + (fold_constr f r c)
      | _ -> fold_constr f r c) in
    fold_constr f 0 c

let can_fertilise annotated_term g =
  (* Returns true when a given side of an annotated equation can be weak fertilised*)
  let can_fertilise_side equation_side =
    match kind_of_term equation_side with
    App (c,al) when c = !wave_out || c = !wave_in ->
      (* Can weak fertilise when head term is a wave front that contains one wave hole *)
      num_wave_holes al.(1) = 1
      (* Can weak fertilise when term has no annotated differences
      (we assume this when no holes are found *)
    | _ -> num_wave_holes equation_side = 0
  in
  try
    let (lhs, rhs) = get_sides_of_equation annotated_term g in
    let l = can_fertilise_side lhs in
    let r = can_fertilise_side rhs in
    l || r
  with Occur ->
    (* Non-equation. Can only strong fertilise if there are no difference annotations *)
    num_wave_holes annotated_term = 0

let fertilise_with_all givens =
  let s = map (fun x ->
  let arg = valueIn (VConstr ([],x)) in
  (interp <:tactic<( (fert2 $arg); let x := $arg in clear x)>>)) givens in
  tclTHENSEQ s

let list_max f x =
  match x with
    [] -> anomaly("list_max: empty list not expected")
  | h::t -> (fold_left (fun sofar h -> if f h sofar then h else sofar) h t)

let unique_subterms c = remove_duplicates (=) (collect_subterms c)

open Autorewrite

(* For each possible way to use a rewrite once, the rewrite is applied and a supplied tactic t is called.
   If t fails, another rewrite position is tried. *)
let rec rewrite_one_occurance (rew:rew_rule) n callback_tactic side_condition_tactic g =

  (* Fast but no setoid support *)
  let rewrite = rewrite_at rew.rew_lemma rew.rew_l2r n in

  (* Slow but supports setoids *)
  (* let rewrite = Rewrite.cl_rewrite_clause (inj_open rew.rew_lemma) rew.rew_l2r (true, [n]) None(*in conclusion*) in *)

  (* Quite slow, supports setoids, only finds some occurances, sometimes adds evars causing errors *)
  (* let rewrite = Equality.general_rewrite rew.rew_l2r (true, [n]) (rew.rew_lemma)  (*None*) in *)

  (* Only allow rewrite if side-conditions are solveable *)
  let rewrite = tclTHENSFIRSTn rewrite [|tclIDTAC|] (tclSOLVE [side_condition_tactic]) in
  (* Tries to rewrite at nth position, incrementing n each attempt. When the rewrite tactic fails, we
  use this to indicate that all positions have been tried. Would be faster to generate all rewrite matches in
  one go but this trick works well enough. *)
  tclORELSESEQ[
    tclORELSESEQ[
      tclTHENSEQ [
        tclORELSESEQ[
          rewrite;
          (* Called when rewriting at an invalid position. "fail 1" so that no more positions are tried *)
          tclFAIL 1 (str "")
        ];
        (* (fun g -> dmsg 0 (str "rewrite " ++ (pr_constr rew.rew_lemma) ++ str (" at " ^ (string_of_int n))); tclIDTAC g); *)
        callback_tactic
      ];
      (* Try rewriting at next position *)
      rewrite_one_occurance rew (n + 1) callback_tactic side_condition_tactic];

      tclFAIL 0 (str "All rewrite positions tried")
  ] g

(* Using a lemma database, tries all ways to rewrite once with a lemma and then calls a
callback tactic, backtracking on failure. *)
let autorewrite_occurances base callback_tactic side_condition_tactic g =
  (* FIXME: Doesn't find matches for some sum, app and rev rules for some reason *)
  (* Use discrimination net to filter rules that could apply *)
  (*
  let conclusion_subterms = unique_subterms (pf_concl g) in
  let rew = fold_left (fun sofar subterm -> dmsgc 0 "st" subterm; (Autorewrite.find_matches base subterm) @ sofar)
    [] conclusion_subterms in
  let rewrites = remove_duplicates (=) rew in
  *)

  let rew = fold_left (fun acc base -> try (Autorewrite.find_rewrites base) @ acc with _ -> acc) [] base in
  let rewrites = map (fun x -> (*dmsgc 0 "rew_lem" x.rew_lemma;*) rewrite_one_occurance x 1 callback_tactic side_condition_tactic) rew in
  tclORELSESEQ rewrites g

TACTIC EXTEND findrewrites
| [ "find_rewrites" tactic(t)] -> [ autorewrite_occurances ripple_all_db (snd t) tclIDTAC]
END

(* Adds bash terminal color codes for rippling annotations *)
let color_annotation measure c =
 let string_of_ppcmds p = Pp.pp_with Format.str_formatter p; Format.flush_str_formatter() in
 let s = string_of_ppcmds (pr_constr c) in
  (* 40=black bg, 42=green bg, 27=green text, 37=white text*)
  (* let diff_color = "\027[42m" in *)
  let diff_color = "\027[1;32;42m" in
  let in_color = "\027[1;30;45m" in
  let sink_color = "\027[0;30;44m" in
  let skel_color = "\027[0;30;47m" in
  let color_off = "\027[0m" in

  (* Find rippling annotations and color them. Need to be careful of regexp's greedy matching *)
  (* Any character sequence but double underscore *)
  let p = "\\(\\(_[^_]\\|[^_]\\)*\\)" in
  let s = Str.global_replace (Str.regexp ("<|" ^ p ^ "__")) (diff_color ^ "<\\1" ^ skel_color) s in
  let s = Str.global_replace (Str.regexp ("__" ^ p ^ "|>")) (diff_color ^ "\\1>" ^ skel_color) s in
  let s = Str.global_replace (Str.regexp (">|" ^ p ^ "__")) (in_color ^ ">\\1" ^ skel_color) s in
  let s = Str.global_replace (Str.regexp ("__" ^ p ^ "|<")) (in_color ^ "\\1<" ^ skel_color) s in
  let s = Str.global_replace (Str.regexp ("&\\(\\([^&]\\)*\\)&")) (sink_color ^ "\\1" ^ skel_color) s in

  let s = Str.global_replace (Str.regexp "\n") "" s in (* workaround to remove newlines string_of_ppcmds adds sometimes*)
  str (measure_list_to_string measure) ++ str " " ++ str skel_color ++ str s ++ str color_off

(* Latex formatting for annotations
   TODO: Refactor this function with other formatting functions
*)
let color_annotation_latex measure c =
 let string_of_ppcmds p = Pp.pp_with Format.str_formatter p; Format.flush_str_formatter() in
 let s = string_of_ppcmds (pr_constr c) in

  (* Find rippling annotations and color them. Need to be careful of regexp's greedy matching *)
  (* Any character sequence but double underscore *)
  let p = "\\(\\(_[^_]\\|[^_]\\)*\\)" in

  (* Remove excessive bracketing *)
  let s = Str.global_replace (Str.regexp "(__") "__" s in
  let s = Str.global_replace (Str.regexp "__)") "__" s in
  let s = Str.global_replace (Str.regexp "(&") "&" s in
  let s = Str.global_replace (Str.regexp "&)") "&" s in
  (* Remove brackets at start and end of expression *)
  let s = Str.global_replace (Str.regexp "^(") "" s in
  let s = Str.global_replace (Str.regexp ")$") "" s in
  (* Remove brackets at start and end of expression *)
  let s = Str.global_replace (Str.regexp ")$") "" s in

  let s = Str.global_replace (Str.regexp "\n") "" s in (* workaround to remove newlines string_of_ppcmds adds sometimes*)
  let s = Str.global_replace (Str.regexp ("<| " ^ p ^ "__ ")) "!\\wo{\\lstinline!\\1! \\wh{\\lstinline!" s in
  let s = Str.global_replace (Str.regexp (" __" ^ p ^ " |>")) "!} \\lstinline!\\1!}\\lstinline!" s in
  (*let s = Str.global_replace (Str.regexp (">|" ^ p ^ "__")) "!\n\\ri{\\lstinline!\\1!}{\\lstinline!" s in
  let s = Str.global_replace (Str.regexp ("__" ^ p ^ "|<")) "!}{\\lstinline!\\1!}\\lstinline!" s in*)
  let s = Str.global_replace (Str.regexp ("&\\(\\([^&]\\)*\\)&")) "!\\rs{\\lstinline!\\1!}\\lstinline!" s in

  (* terms outside annotations need annotating *)
  let s = "\\lstinline!" ^ s ^ "!" in

  (* remove excessive spacing inside lstinline terms *)
   let s = Str.global_replace (Str.regexp " !") "!" s in
   let s = Str.global_replace (Str.regexp "! ") "!" s in
   let s = Str.global_replace (Str.regexp "[ ]*\\\lstinline!!") "" s in

  (* add newline to middle of equations *)
   let s = Str.global_replace (Str.regexp "!=!") "!=!\n" s in
   str s

exception Untestable of Pp.std_ppcmds

type given_data = {id:constr; term:constr; threshold:int list}

(* Ripples towards and attempts to fertilise with list of givens *)
let rippling_rewrite bas (given2 : given_data list) target_term allow_fertilisation side_condition_tactic g =

  (* FIXME: Hack of putting dsum measure in a list so list measure functions work with it *)
  let measure_list x = [dsum_measure x] in

  let get_worst_measure skeleton erasure g =
    let annotations = annotate erasure skeleton g in
    let measures = combine annotations (map measure_list annotations) in
    if measures = [] then raise No_embeddings;
    list_max (fun x y -> measure_list_increasing (snd y) (snd x)) measures
in

  let conclusions_seen = ConstrMap.create 10 in

   (* Try to weak fertilise with all givens *)
   let weak_fertilise given g = tclTHENSEQ[
      (let given_ids = map (fun x -> x.id) given in fertilise_with_all given_ids)] g
    in

  (* Applies tactic t and calls f() if t succeeds. Useful for debugging and success messages *)
  let if_solved t f = (fun g -> let t_call = t g in if all_goals_solved t_call then f(); t_call) in

  let strong_fertilise given g =
    (* Try to strong fertilize with only the first given. If there are multiple different givens, rippling will
       not get to the stage of strong fertilizing with just one of them as the others will no longer embed *)
    if_solved
      (match given with
      [] -> anomaly("given expected")
      | x::_ ->
        let arg = valueIn (VConstr ([],x.id)) in
        (interp <:tactic<let a := $arg in apply a>>)) (* "apply" will instantiate sinks, unlike "assumption" *)
      (fun () -> dmsg 0 (str "Strong fertilized!")) g
  in

  let fertilise given = tclFIRST[strong_fertilise given; weak_fertilise given] in
  (* If rule contained a pattern matching construct, eliminate it (possibly producing subgoals, some of which may
     no longer embed but have trivial proofs *)
  let case_split =
       tclTHENSEQ [
         (*case_concl;*)
         (* Allow any case splits possible *)
         (case_concl2 (fun arg -> (interp <:tactic<case_eq2 $arg >>)));
         interp <:tactic<intros; try subst>>
         ] in

  let rec go given rule_db depth previous_conclusion g =
    (* Fail if conclusion has been seen before *)
    (* Equational conclusions treated as special cases: only allow one side of the equation to change if
      what it is being changed to has not been seen before. Improves performance but could block proofs
      where a rule applies to the whole equation. *)
    let loop_detect previous_conclusion g =
      let check_if_already_visited conclusion =
        try
          ignore (ConstrMap.find conclusions_seen conclusion); raise Already_seen
        with Not_found ->
          ConstrMap.replace conclusions_seen conclusion () in
      let conclusion = pf_concl g in
      try
        check_if_already_visited conclusion;
        (match (kind_of_term previous_conclusion, kind_of_term conclusion) with
          (App (f1, [|t1; lhs1; rhs1|]), App (f2, [|t2; lhs2; rhs2|]))
            when f1 = Lazy.force eq_ind && f2 = Lazy.force eq_ind ->
            if lhs1 <> lhs2 then check_if_already_visited (mkApp (f1, [|t1; lhs2; mkProp|]));
            if rhs1 <> rhs2 then check_if_already_visited (mkApp (f1, [|t1; mkProp; rhs2|]));
        | _ -> ()); (* FIXME: need to store assumptions too or things will break for certain goals *)
        tclIDTAC g
      with Already_seen ->
        let s = str "Already seen: " ++ pr_constr (conclusion) in
        if show_pruned_ripple_step then dmsg 0 s;
        tclFAIL 0 s g
    in

    let allow_transition g = (
      let conclusion_after = pf_concl g in

      match given with
      [] -> anomaly ("No givens to ripple with")
      | _ ->
        try
          let generate_measures given_data =
            let t = given_data.term in
            let after = annotate conclusion_after t g in

            if after = [] then
              raise No_embeddings
            else
            (
              (* Compare worst measure from before transition with best measure from after *)
              let after_ann_measures = combine after (map measure_list after ) in
              let threshold = given_data.threshold in

              if display_all_transition_annotations then
                (
                iter (fun (x,y) -> dmsg 0 ((str "Reduction check: ") ++ (color_annotation y x) ++ str " threshold " ++ str (measure_list_to_string threshold))) after_ann_measures);

              (* Only measures that better than the threshold or equal are allowed (for multiple givens, only the measure of one given
                has to improve each time as long as the others do not get worse *)
              let after_ann_measures =
                filter (fun x ->
                 measure_list_decreasing threshold (snd x) || snd x = threshold) after_ann_measures in
              if after_ann_measures = [] then (raise Not_reducing);

              (* Should this transition be OK, pick worst measure of those that are left to get the one closest to the threshold
                 to generate the new threshold *)
              let (righta, rightm) = list_max (fun x y -> measure_list_increasing (snd y) (snd x) && snd x <> threshold) after_ann_measures in

              dmsg 0 (color_annotation rightm (righta));
              (* iter (fun (x,y) -> dmsg 0 ((str "after filtered ") ++(pr_constr x) ++ (str " ") ++ str (measure_list_to_string y))) after_ann_measures; *)
              (* dmsg 0 ((str "dsum: ") ++ str (string_of_int (dsum_measure righta))); *)
              ({given_data with threshold = rightm}, (threshold, rightm))
            ) in

          let given_annotations = map generate_measures given in

          let (new_given_data, given_measures) = List.split given_annotations in

          (* Measure reducing if at least one given measure gets better and the rest do not get any worse *)
          let decreasing = List.fold_left
            (fun sofar (leftm, rightm) ->
            let d = measure_list_decreasing leftm rightm in
            if display_all_transition_annotations then dmsg 0 (str (if d then "Reduces for this given" else "Not reducing for this given"));
            d || sofar)
            false given_measures in

          if not decreasing then
            raise Not_reducing
          else
            Some new_given_data
    with
    | Not_reducing -> let s = str "Not reducing" in if show_pruned_ripple_step then dmsg 0 s; None
    | No_embeddings ->
      (*dmsg 0 (
        (str "Could not generate embeddings or find reducing measure for this transition: ") ++
        (*(pr_constr conclusion_before) ++*) (str " => ") ++ (pr_constr (pf_concl g)));*)
      let s = str "No embeddings: " ++ (pr_constr conclusion_after) in if show_pruned_ripple_step then dmsg 0 s; None
    )
   in

  (* checks if this is a ripple step and, if so, generates the next transitions *)
  let next_transitions goal_from_case_split g =
    (if show_pruned_ripple_step then dmsg 0 ((str "Transition: ") ++ pr_constr (pf_concl g)));
    match allow_transition g with
      None ->
        (* Subgoal from case split might not have embeddings but can be solved trivially *)
        (if goal_from_case_split then tclSOLVE [side_condition_tactic] (* if you allow failure here and goals with embeddings become fertilised, this subgoal will remain when rippling is finished. Sometimes these subgoals won't be provable if a bad case
        split is made! *)
          else tclFAIL 0 (str "Transition not being allowed")) g
    | Some new_given_data ->
        (let callback = go new_given_data (rule_db) (depth + 1) (pf_concl g) in
         tclORELSESEQ[
          autorewrite_occurances bas callback side_condition_tactic; (* look for other ripple steps... *)
          fertilise given (* ...and try fertilisation when there are none *)
(*           tclTHENSEQ[fertilise given; (fun g -> dmsg 0 ((str "ripple depth ") ++ (str (string_of_int depth))); tclIDTAC g) ] *)
          ] g)
      in

  if (depth > max_ripple_depth + 1 (* +1 to indent logging correctly*)) then
    (dmsg 0 (str "Depth limit."); tclFAIL 0 (str ("rippling depth exceeded")) g)
  else
  (
    tclIFTHENELSE case_split
      (tclTHENSEQ[tclPRINTGOAL "cs"; loop_detect previous_conclusion; next_transitions true])
      (tclTHENSEQ[loop_detect previous_conclusion; next_transitions false])
    g
  )
in
  let initial_conclusion = pf_concl g in
  let given3 =
    try
     dmsg 0 (str ("Rippling with " ^ (string_of_int (length given2)) ^ " given(s)"));
     map (fun x ->
      let (annotation, measure) = get_worst_measure x.term initial_conclusion g in
        dmsg 0 (color_annotation measure annotation);
       {x with threshold = measure}) given2
    with No_embeddings -> [] in

  if given3 = [] then
    tclFAIL 0 (str "All supplied givens do not initially embed into the conclusion") g
  else
  (
(*
    let ripple_step =
      (* can sometimes fertilise before performing ripple steps *)
      tclTHENSEQ[tclTRY (strong_fertilise given3);
      go given3 bas 1 initial_conclusion;
      tclTRY (fertilise given3)]
      in
    autorewrite_occurances bas ripple_step side_condition_tactic g
*)

    let ripple_step =
      (* can sometimes fertilise before performing ripple steps *)
      tclTHENSEQ[
      go given3 bas 1 initial_conclusion;
      tclTRY (fertilise given3)]
      in
      tclTHENSEQ[tclTRY (strong_fertilise given3);
    autorewrite_occurances bas ripple_step side_condition_tactic] g

  )

let rippling bas given side_condition_tactic =
  let given = map (fun (id, term) -> {id=id; term=term; threshold=[]}) given in
  rippling_rewrite bas given None true side_condition_tactic

(* Returns number of occurances of a subterm within a term *)
let count_occurances term term_to_count =
  let rec count acc c =
    (if eq_constr c term_to_count then
      fold_constr count (acc + 1) c
    else
      fold_constr count acc c)
  in
  count 0 term

(* Generalises common subterms in the conclusion. *)
let generalise_goal' generalise_apart gl =
  let allow_generalisation_of_constants = true in
  let subterm_must_occur_on_both_sides_of_equation = false in

  (* Creates [start; start + 1; ...; start + len] number sequence *)
  let rec sequence start len = if len <= 0 then [] else start :: sequence (1 + start) (len - 1) in

  (* Removes terms that are subterms of other terms in the list *)
  let remove_occurs checking_terms all_terms =
    let occurs_term_list term term_list = exists (fun t -> t <> term && occur_term term t) term_list in
    filter (fun t -> not (occurs_term_list t all_terms)) checking_terms
  in

  (* Get LHS/RHS of equation *)
  (* TODO: Should support non-equations *)
  match kind_of_term (pf_concl gl) with
    App (f,[|_; lhs; rhs|]) when f = Lazy.force eq_ind ->
    (
    (* Identifies generalisation candidates *)
    let candidate = fun t ->
      (not (isProd (pf_type_of gl t))) && (* term isn't a proposition e.g. int -> int *)
      (not (is_Type (pf_type_of gl t))) && (* term isn't e.g. A of type Type from a "list A" term *)
      (not (is_Set (pf_type_of gl t))) && (* term isn't a type like "nat", "list nat" (these are used as function parameters) *)
      (allow_generalisation_of_constants || (occur_variable_term t)) && (* term contains a variable somewhere *)
      (subterm_must_occur_on_both_sides_of_equation || (occur_term t rhs)) (* term occurs on RHS of equation *)
    in

    (* Identify terms to generalize *)
    let lhs_terms = (collect_subterms lhs) in
    let lhs_filtered = (filter candidate lhs_terms) in
    let lhs_filtered = removeconstrdups lhs_filtered in
    let to_generalize = remove_occurs lhs_filtered lhs_filtered in

    (* iter (dmsgc 0 "to generalize") to_generalize;  *)
    (* Identify which of these terms should be generalised everywhere and which should be be generalised apart
      e.g. (x+1) + (x+1) = (x+1) * 2 can be generalised everywhere to n + n = n * 2
      e.g. (x+1) + (x+1) = (x+1) + (x+1) can be generalised apart to x + y = x + y *)
    (* Count occurances of each candidate term on LHS and RHS *)
    let to_generalize_count = map (fun t -> (t, (count_occurances lhs t), (count_occurances rhs t))) to_generalize in

    (* Term that occur more than once and the same number of times on both sides of the equation should
      be generalized apart and others are generalized everywhere *)
    if generalise_apart then
    (
      let (to_generalize_apart, generalise_everywhere) =
      partition (fun (t, l, r) -> l = r && l > 1) to_generalize_count in

      (* Generate tactic for generalizing candidates apart *)
      (* The generalize tactic wants the term to generalize and in which positions. Given
      this equation and positions:

        x + x + x = x + x + x
        1   2   3   4   5   6

      To generalise the 3 terms on each side apart, we want to generalize at position 1,4,
      2,5 and 3,6. As we need to call the generalize tactic for each pair, the valid positions
      of x will change each time. Therefore we need to generalize at position 1,4, 1,3 then 1,2.
      *)
      let to_generalize_apart =
        map (fun (t, l, r) ->
          fold_left (fun r x ->
            let lhs_position = 1 in
            let rhs_position = (l + 2) - x in
            r @ [(((true,[lhs_position; rhs_position]), t), Names.Anonymous)] ) [] (sequence 1 l))
        to_generalize_apart in
      let to_generalize_apart = flatten to_generalize_apart in
      let apart_tactic = map (fun t -> generalize_gen [t]) to_generalize_apart in
      tclTHENSEQ apart_tactic gl
    )
    else
    (
      let generalise_everywhere = to_generalize_count in
      (* Do not generalise a term that is a single variable. This is OK when generalising apart though *)
      let is_variable_term t = (isConst t) || (isVar t) in
      let generalise_everywhere = map (fun (t, _, _) -> t ) generalise_everywhere in
      let generalise_everywhere = filter (fun t -> not (is_variable_term t)) generalise_everywhere in
      (* Construct the generalization tactic call *)
      generalize generalise_everywhere gl
    )
  )
| _ -> tclFAIL 0 (str "goal must be an equation") gl

let generalise_goal =
  tclPROGRESS(tclTHENSEQ[
    interp <:tactic<try f_simp>>;(* inverse functionality *)
     (* Must call "intros" on variables introduced from generalisating for next generalization round to work *)
     (* Recursively generalize common subterms *)
     tclREPEAT (tclTHEN (generalise_goal' false) (interp <:tactic<intros>>));
     (* Generalize apart *)
     tclTRY (tclTHEN (generalise_goal' true) (interp <:tactic<intros>>));
     (* tclPRINTGOAL "After generalising"; *)
    ])

(* FIXME: use fold for this*)
let get_vars c =
 let subterms = (collect_subterms c) in
 let vars = removeconstrdups (filter isVar subterms) in
 vars

let induction_on_nth_var2 n gl =
  let vars = get_vars (pf_concl gl) in
  if (n >= length vars) then
    tclFAIL 0 (str ("Not enough variables to pick variable " ^ (string_of_int n))) gl
  else
    let id = nth vars n in
     (* Generalize all variables we can before we start induction *)
     (* Induction could fail after we generalize. *)
      tclTHENSEQ [
        revert_except id;
        Tactics.default_elim false (id, Rawterm.NoBindings)
      ]
     gl

let induction_on_nth_var n =
  tclTHENSEQ [
    interp <:tactic<intros>> ; (* Intro all variables first so they can be reverted as required *)
    (induction_on_nth_var2 n);
    interp <:tactic<intros>> (* Intro in all subgoals. This makes the step case more readable when this tactic is used interactively *)
  ]

(* Returns list of assumptions that embed in to the goal. Only assumptions of Prop type are
considered, otherwise e.g. nat and list nat assumptions could be considered targets for rippling
towards, which is unlikely to be useful  *)
let get_embeddable_assumption g =
  let ids = (pf_ids_of_hyps g) in
  let em_ids =
   filter (fun h ->
    let hyp_typ = pf_get_hyp_typ g h in is_Prop (pf_type_of g hyp_typ) && embeds hyp_typ (pf_concl g) g
    ) ids in
  map (fun c -> mkVar c) em_ids

TACTIC EXTEND inductionnth
| [ "induction_nth" natural(n) ] -> [ induction_on_nth_var n ]
END

(* copy/paste from tactics/inv.ml *)
let var_occurs_in_pf gl id =
  let env = pf_env gl in
  occur_var env id (pf_concl gl) or
  List.exists (occur_var_in_decl env id) (pf_hyps gl)

(* Removes assumptions that do not share variables with the conclusion *)
(* Limitation: assumptions such as 1 = 0 will be marked as irrelevant and removed! *)
let irrelevant gl =
  let hyps = pf_hyps gl in
  let env = pf_env gl in
  (* Get assumption variables that occur in the conclusion *)
  let (used, not_used)= List.partition (fun (id,_,_)->occur_var env id (pf_concl gl)) hyps in

  (* This step is to prevent e.g. y being marked as used because it uses A like the conclusion: A:Set, x:list A, y:list A |- x = x*)
  let used2 = List.filter (fun (_,_,t)-> not (is_Prop t or is_Set t or is_Type t)) used in
  (* dmsg 1 "USED2";List.iter (fun (x,y,z)->dmsg 1 (string_of_id x)) used2;  *)

  (* Collect all assumption variables that use conclusion variables, then all the variables that use these etc. *)
  let rec collect used not_used =
  (* dmsg 1 "USED";List.iter (fun (x,y,z)->dmsg 1 (string_of_id x)) used; *)
  (* dmsg 1 "NOT USED";List.iter (fun (x,y,z)->dmsg 1 (string_of_id x)) not_used; *)

  (* Unused vars become used if the id of a used var occurs in the type of the former e.g. if x:nat is used,
    y:(x=1) will become used because x occurs in y *)
  let (new_used, new_not_used) =
    List.partition (fun (id,_,var_type) ->
                      List.exists (fun (id2,_,_) -> occur_var env id2 var_type) used) not_used in
    if new_used = [] then
      not_used
    else(
      let (new_used2, new_not_used2) =
        List.partition (fun (x,y,z)->(List.exists (fun (_,_,var_type) ->(occur_var env x var_type)) new_used)) new_not_used in
      collect (used@new_used@new_used2) new_not_used2)
  in
  let vars_to_clear = List.map (fun (x,y,z)->x) (collect used2 not_used) in
  Hiddentac.h_clear false vars_to_clear gl

TACTIC EXTEND irrelevant
| ["irrelevant" ] -> [ irrelevant ]
END

let find_or_none id =
  try Some
    (match Nametab.locate (make_short_qualid id) with ConstRef c -> c | _ -> Util.anomaly "Not a constant")
  with Not_found -> None

(* Tries to create a reference to a Coq constant from a name (e.g. from the name of a Coq function that's been declared like "plus") *)
let find_or_none id =
  match Nametab.locate (make_short_qualid id) with ConstRef c -> c | _ -> Util.anomaly "Not a constant"

(* Generates equations from Coq functions and optionally adds these to a lemma database *)
let generate_function_wave_rules fun_name add_to_db =
(* FIXME: Command disabled because it's causing makefile problems! *)
  let fas = [((get_fresh_theorem_name "functionalinduction"),fun_name,Rawterm.RProp Term.Pos)] in
  (* Taken from indfun_main.ml4. Should refactor this. *)
  (*****)
  (try
    Functional_principles_types.build_scheme fas
   with Functional_principles_types.No_graph_found ->
  match fas with
    | (_,fun_name,_)::_ ->
        begin
    Indfun.make_graph (Nametab.global fun_name);
    try Functional_principles_types.build_scheme fas
    with Functional_principles_types.No_graph_found ->
      Util.error ("Cannot generate induction principle(s)")
        end
    | _ -> assert false (* we can only have non empty  list *));
  (*****)

  Lemmas.start_proof
    (get_fresh_theorem_name "dummy")
    (Decl_kinds.Global,(Decl_kinds.Proof Decl_kinds.Theorem))
    (Typeops.type_of_constant(*Environ.constant_value*) (Global.env())
      (* We rely on functional principles module generating a lemma named ..._equation here *)
      (find_or_none (id_of_string ((Libnames.string_of_reference fun_name) ^ "_equation"
       ))))
    (fun _ _ -> ());

     let case_split = tclTHENSEQ [
           interp <:tactic<intros>>;
           case_concl2 (fun arg -> (interp <:tactic<case_eq2 $arg >>))] in (* FIXME: not sure why, but it fails when splitting on innermost case *)
(*            interp <:tactic<intros; try subst>>] in *)

      Pfedit.by (
         tclTHENSEQ [
         (*tclPRINTGOAL "Top-level goal: ";*)
          interp <:tactic<intros>>;
          tclTRY case_split;
          tclPRINTGOAL "Subgoal: ";
            (lemma_cache ((Libnames.string_of_reference fun_name)^"_waverule")
                 (interp <:tactic<try reflexivity; try tauto>>) (Some ripple_basic_db))
          ]);
  Lemmas.save_named false;
  ()

VERNAC COMMAND EXTEND AddWaveRule
[ "AddWaveRule" reference(fun_name) ] -> [ generate_function_wave_rules fun_name true ]
END

(* Adds lemma id as new rule (if applicable) for rippling, trivial and simplification *)
(* FIXME: Should be a command. *)
TACTIC EXTEND AddHint
| [ "AddHint" ident(id) ] -> [ fun g -> auto_add_hint id (Some ripple_cached_db) g; tclIDTAC g ]
END

(* "trivial" tactic that does not use the "core" database *)
TACTIC EXTEND AutoWithoutCore
| [ "auto_without_core" "with" preident_list(bl) ] -> [ Auto.auto ~use_core_db:false !Auto.default_search_depth [] bl ]
END

(* A less verbose printer for autorewrite databases *)
let custom_print_rewrite_hintdb bas =
  ppnl (str "Database " ++ str bas ++ Pp.fnl() ++
     prlist_with_sep Pp.fnl
     (fun h ->
       str (if h.Autorewrite.rew_l2r then "=> " else "<= ") ++
         Printer.pr_lconstr h.Autorewrite.rew_lemma ++ str " : " ++ Printer.pr_lconstr h.Autorewrite.rew_type ++
         (if h.Autorewrite.rew_tac <> Tacexpr.TacId [] then
            (str " then use tactic " ++ Pptactic.pr_glob_tactic (Global.env()) h.Autorewrite.rew_tac)
          else
            (str "")))
     (Autorewrite.find_rewrites bas))

VERNAC COMMAND EXTEND CustomPrintHints
| [ "PrintHints" preident(b) ] -> [ custom_print_rewrite_hintdb b ]
END

let ripple given lemma_dbs side_condition_tactic g =
    iter (fun x -> dmsgc 1  "Rippling with variable " x;
      dmsgc 1 "rippling with variable type " (pf_type_of g x)) given;
    tclFIRST [rippling lemma_dbs (map (fun x -> (x, (pf_type_of g x))) given) side_condition_tactic;
              fertilise_with_all given] g (* try to fertilise if we couldn't ripple at all *)

let auto_ripple lemma_dbs side_condition_tactic g =
  let given = get_embeddable_assumption g in
  match given with
    [] -> tclIDTAC_MESSAGE (str "no assumptions that require rippling") g
  |  _ -> ripple given lemma_dbs side_condition_tactic g

(* For each of the deepest subterms, try to reduce the subterm and if it did not reduce, reduce
   the parent subterm etc. until a term is reduced. Using this gives useful but concise step
   by step reduction traces e.g.
   (1 + 2) + (3 + 4) + 5 = 15
   3 + 7 + 5 = 15
   10 + 5 = 15
   15 = 15
*)
let rec simpl_step f o =
  match kind_of_term o with
  (* These terms cannot be reduced *)
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _ | Construct _) -> o
  | _ ->
    let r = simpl_step f in
    let s = map_constr r o in
    if (s = o) then (f o) else s

TACTIC EXTEND simplstep
| [ "simpl_step" ] -> [
  fun g ->
    let reduce = pf_compute g in
    let s = simpl_step reduce (pf_concl g) in
    Hiddentac.h_change None s onConcl g]
END

TACTIC EXTEND ripplingtactics
| [ "ripple" constr(given) ] -> [
  fun g ->
    (dmsg 1 (str "############## Starting rippling");
     let r = rippling ripple_all_db [ (given, (pf_type_of g given))] (default_side_conditions_tactic) in
   r) g]
| [ "ripple" ] -> [ auto_ripple ripple_all_db default_side_conditions_tactic]
END

(* Rippling using only basic definitions *)
TACTIC EXTEND ripplingtactics2
| [ "ripple'" ] -> [ auto_ripple [ripple_basic_db] default_side_conditions_tactic]
END

TACTIC EXTEND generalisegoal
| [ "generalise_goal" ] -> [ generalise_goal ]
| [ "lemma_cache" tactic(t)] -> [ lemma_cache "userhint" (snd t) (Some ripple_cached_db)]
END

TACTIC EXTEND LatexPrint
| ["latex_annotate" ] -> [
  fun g ->
  let givens = get_embeddable_assumption g in
  let annotations = map (fun x -> annotate (pf_concl g) (pf_type_of g x) g) givens in
  let annotations = map hd annotations in

  msgnl (str "");
  msgnl (str "\\begin{quote}");
  iter (fun x ->
    (* remove start and end brackets *)
    let s = string_of_ppcmds (pr_constr (pf_type_of g x)) in
    let s = Str.global_replace (Str.regexp "^(") "" s in
    let s = Str.global_replace (Str.regexp ")$") "" s in

    msgnl ((str "\\lstinline!") ++ (pr_constr x) ++ (str " : ") ++ str s ++ (str "!\\\\"))) givens;
  msgnl (str "\\coqgoalline");
  iter (fun x -> msgnl (color_annotation_latex [0] x)) annotations;
  msgnl (str "\\end{quote}");
  tclIDTAC g
  ]
END

TACTIC EXTEND embeddingstactics
 ["measure_progress" constr(skel) constr(x) constr(y) ] -> [
  fun g -> let r = measure_progress skel x y g
  in (if r then msgnl(str "PROGRESS") else msgnl(str "NO PROGRESS"));tclIDTAC g]

| ["embeds" constr(x) constr(y) ] -> [
  fun g ->
  msgheading "annotate2";
  let lefta = annotate y x g in
  if (lefta = []) then
    (dmsg 0 (str "No embeddings."); tclFAIL 0 (str "No embeddings.") g)
  else
  (
    iter (fun x -> let m = measure_list x in dmsgc 0 "embedding:" x; (*dmsgc 1 "hole" (find_hole x);*)
               dmsg 0 (str (measure_list_to_string m))) lefta;
    tclIDTAC g
  )]

| ["measure_equals" constr(x) string(l) ] -> [
  let m = measure_list x in
  let sm = (measure_list_to_string m) in
  dmsg 1 (str sm);
  if (sm = l) then
    tclIDTAC
  else
    tclFAIL 0 (str "Measure for " ++ (pr_constr x) ++ str (" is " ^ sm ^ " when it was expected to be " ^ l))
  ]

| ["all_embeddings_found" constr(x) constr(y) ne_constr_list(expected)] -> [
  fun g ->
  let annotations = annotate y x g in
  let unfound_expected = fold_left (fun r a -> if exists (eq_constr a) annotations then (dmsgc 1 "found" a;r) else a::r) [] expected in
  let unexpected = fold_left (fun r a -> if exists (eq_constr a) expected then r else a::r) [] annotations in
  iter (fun x -> dmsgc 1 "expected annotation not found" x) unfound_expected;
  iter (fun x -> dmsgc 1 "unexpected annotation" x) unexpected;

  if unfound_expected = [] && unexpected = [] then
    tclIDTAC g
  else
    tclFAIL 0 (str "Embeddings list not exhaustive and/or contains invalid embeddings.") g
]

END

TACTIC EXTEND MeasureDsumEquals
["measure_dsum_equals" constr(x) string(l) ] -> [
  let m = [dsum_measure x] in
  let sm = measure_list_to_string m in
  dmsg 1 (str sm);
  if (sm = l) then
    tclIDTAC
  else
    tclFAIL 0 (str "dsum measure for " ++ (pr_constr x) ++ str (" is " ^ sm ^ " when it was expected to be " ^ l))
  ]
END

TACTIC EXTEND fertilisetactic
| ["fertilise" ] -> [ fun g->
  let given = get_embeddable_assumption g in
  match given with
   [] -> tclIDTAC_MESSAGE (str "No assumptions that require rippling") g
  | _ -> fertilise_with_all given g
 ]
END

TACTIC EXTEND ocaml_term_tactic
(* Displays OCaml representation of Coq term. Useful for understanding term construction for writing OCaml tactics. *)
| [ "ocaml_term" constr(t) ] -> [
dmsg 0 (str (string_of_bool (is_constant t)));
 constr_display t;
print_pure_constr t;
tclIDTAC ]
END

TACTIC EXTEND myrewrite_tactic
| [ "myrewrite" orient(o) constr(t) "at" integer(n) ] -> [
rewrite_at t o n
]
END

(* Renames id x to y with postfix s. *)
TACTIC EXTEND rename1
| ["rename_after" hyp(x) ident(y) string(postfix)] -> [
  fun g ->
    let i = fresh_id (pf_ids_of_hyps g) (id_of_string ((string_of_id y) ^ postfix)) g in
    Tactics.rename_hyp [(x, i)] g
]
END

TACTIC EXTEND initrippling
| ["init_rippling" constr(wave_out2) constr(wave_in2) constr(wave_hole2) constr(wave_sink2) constr(fertilise_rewrite2)] -> [
  wave_out := wave_out2; wave_in:= wave_in2; wave_hole := wave_hole2; wave_sink:= wave_sink2; fertilise_rewrite := fertilise_rewrite2;tclIDTAC ]
END

(******************************************)
(* FIXME: Copy/pasted from refiner.ml. Should just expose these in refiner.mli if unmodified here *)
let hypotheses gl = gl.evar_hyps
let conclusion gl = gl.evar_concl
(* various progress criterions *)
let mysame_goal gl subgoal =
  eq_named_context_val (hypotheses subgoal) (hypotheses gl) &&
  eq_constr (conclusion subgoal) (conclusion gl)

let myweak_progress gls ptree =
  (List.length gls.it <> 1) or
  (not (mysame_goal (List.hd gls.it) ptree.it))

(* Il y avait ici un ts_eq ........ *)
let myprogress gls ptree =
  (myweak_progress gls ptree) or
  (not (ptree.sigma == gls.sigma))

(*****************************************)

let seen_conjectures = ConstrMap.create 10

TACTIC EXTEND inductiveproofautomation
(* Top-level inductive proof automation tactic *)
| [ "super" (*constr(given)*) natural(maxdepth) tactic(easy) tactic(simplify) tactic(quickcheck) natural(cache_lemmas)
    "with"  ne_preident_list(lemma_dbs) ] -> [

  let rec super depth g =

  ConstrMap.replace seen_conjectures (mkRel 1) ();
  (* Tries induction on the 1th variable, tries the waterfall on the goals. If this fails, tries the 2nd variable, then 3rd etc. *)
  let rec induction_all n =
    (if n < 0 then
      []
    else
      let wf = tag_tclTHENSEQ[tclIDTAC(*FIXME:needed for XML to be structured right*); (super (depth + 1))] in
      (* Perform induction, then attempt subgoals with embeddings first. Otherwise, induction is started again when
        a base case cannot be proven trivially. Generally, induction on the "wrong" variable means a step case that fails
        quickly, but proving the base case can lead to a long chain of inductions before backtracking occurs. *)
      let x = tclTHEN (tclTHEN (tag_tactic ("Induction "^(string_of_int n)) (induction_on_nth_var n))
        (fun g -> match get_embeddable_assumption g  with [] -> tclIDTAC g | _ -> wf g)) wf in
      (induction_all (n-1))@[x])
  in

  let indtact g = tag_tclORELSESEQ (induction_all ((length ((get_vars (pf_concl g))))-1)) g in
  let tagged_easy = tag_tactic "Trivial" (tclTRY (snd easy)) in
  let untagged_basic_gen = snd simplify in
  let basic_gen = tag_tactic "Simplify" untagged_basic_gen in
  let generalise_qc =
  tag_tactic "Generalise" (tclTHENSEQ [untagged_basic_gen; generalise_goal; snd quickcheck])
  in

  let cache x =
      (lemma_cache ~add_as_hint:(cache_lemmas <> 0) "cached_subgoal" x (Some ripple_cached_db)) in

  let trivial_generalise_induction =
        tag_tclTHENSEQ [
              untagged_basic_gen;
              tagged_easy;
                tag_tclORELSESEQ [
                  tag_tclTHENSEQ [generalise_qc;cache indtact];
                  (* try again without generalising because overgeneralisations might not be detected *)
                  tag_tclTHENSEQ [basic_gen;cache indtact]
                ]]
                in

  let tagged_base_case = ((*tag_group "No embeddable assumptions"*)  (trivial_generalise_induction)) in
  let ripple_tactic given = (ripple given lemma_dbs (tclTHENSEQ [snd simplify; snd easy])) in
  (* ripples when embeddings are found, nothing otherwise *)
  let tagged_step_case =
    (fun g ->
      let given = get_embeddable_assumption g in
      match given with
        [] -> tclIDTAC g (* ignore this goal if there are no embeddings *)
      | _ -> (*tag_group "Embeddable assumption"*)
          (tag_tclTHENSEQ[
            (* Sometimes step cases are trivial and rippling is not required. No modifications are allowed here so that
               embeddings are maintained *)
            tclTRY (tclSOLVE [tclTHENSEQ[tagged_easy]]);

            tclFIRST
            [
                (if try_simpl_fertilise then
                  (* try to solve goal with trivial tactic, otherwise try to fertilise after simpl *)
                  tclTHENSEQ [interp <:tactic<simpl>>;
                              tclTRY(tclSOLVE[tclTHENSEQ[untagged_basic_gen; snd easy]]);
                              fertilise_with_all given]
                else
                  tclFAIL 0 (str ""));
                (if try_simpl_ripple then
                  tclTHENSEQ [interp <:tactic<simpl; try assumption>>; (* assumption for if we can strong fertilise *)
                              (fun g ->
                                if given = get_embeddable_assumption g then
                                  (* give up if goal contains a match construct as the embeddings algorithm does not treat these correctly *)
                                  tclTHENSEQ[tclTRY (tclTHENSEQ[case_concl; tclFAIL 1 (str "")]); ripple_tactic given]
                                else
                                  tclFAIL 0 (str "")) g]
                else
                  tclFAIL 0 (str ""));
                tag_tactic "Ripple" (ripple_tactic given)
            ];
            trivial_generalise_induction]) g
    ) in

  (* Fails if rippling fails when the goal has embeddings *)
  let tact = tclTHEN tagged_step_case tagged_base_case  in

  (if (depth >= maxdepth) then
      (dmsg 1 (str "Search depth limit reached."); tclFAIL 0 (str "Search depth limit reached."))
     else
     ((tag_tclTHENSEQ [tact]))
  ) g

  in

  let proofname = (string_of_id (Pfedit.get_current_proof_name())) in

  fun g ->

    let starttime = Unix.times() in
    let finished message =
     let s = Printf.sprintf " duration=\"%3.2f\"/>"
      ((Unix.times()).Unix.tms_utime -. starttime.Unix.tms_utime)in

     pp (*indentmsg !indent_level *)((str "<") ++ (str message) ++ (str s) ++   (pr_constr (pf_concl g)));
    log_write "</proof>";

    let s = Printf.sprintf " %3.2f"
      ((Unix.times()).Unix.tms_utime -. starttime.Unix.tms_utime) in

      (*
    indentmsg 0 ((str "\nBenchmark data: ") ++ (str ( proofname ^ " \"")) ++ (str message) ++ (str s) ++ (pr_constr (pf_concl g)) ++ (str "\" ") ++ (str "\n"));
    *)

(*let cg = string_of_ppcmds (pr_constr (pf_concl g)) in*)
let cg = "cannot display" in (* for some reason the above line causes a crash running the tactic within different modules*)

let cg = Str.global_replace (Str.regexp "\n") "" cg in (* workaround to remove newlines string_of_ppcmds adds sometimes*)
indentmsg 0 ((str "\nBenchmark data: ") ++ (str ( proofname ^ " ")) ++ (str message) ++ (str s) ++ (str " \"") ++ (str cg) ++ (str " ")  ++ (str "\" ") ++ (str "\n"));


    close_logfile(); dmsg 1 (str "#### closing logfile") in

  try
    dmsg 1 (str "#### open logfile");
    let methodname = "nocache" in
    open_logfile (proofname ^ "_" ^ methodname);

     indentmsg 0 (str ("<proof name=\""^proofname^"\" description=\"") ++
       (pr_constr (pf_concl g)) ++ (str ("\" method=\"" ^ methodname ^ "\">")));

    let t = fun () ->(
     let r = (*tag_group ("Toplevel")*) (tag_tclTHENSEQ [(*quickcheck_tactic;*)(super 0)]) g in
     finished "SUCCESS";
     r) in

   t()

  with e ->
    (finished "FAILURE"; raise e)
]
END


(***** Quickcheck style counterexample finder *****)

(* Get all the type constructors for a given type *)
let constr_to_constructors t =
  let inductive =
    match kind_of_term t with
    | App (f,args) -> (destInd f, Array.to_list args)
    | Ind (_,_) -> (destInd t, [ ])
    | _ -> anomaly "Expected App or Ind term."
  in
  let inductive_family = make_ind_family inductive in
  get_constructors (Global.env()) inductive_family

let dmsg_constructor_summary c =
  dmsgc 3 "cs_cstr" (mkConstruct(c.cs_cstr));
  List.iter (fun p -> dmsgc 3 "cs_params" p) (c.cs_params);
  Array.iter (fun p -> dmsgc 3 "cs_concl_realargs" p) (c.cs_concl_realargs);
  dmsgc 3 "build_dependent_constructor" (build_dependent_constructor c)

(* Get the type constructor arguments for a given type *)
let get_constructor_argument_types constructor =
  let rel_context = constructor.cs_args in
  let nargs = constructor.cs_nargs in
  let a = Array.make nargs mkProp in
  let index = ref 0 in
  iter_rel_context (fun c -> a.(!index) <- c; index := !index  + 1) rel_context;
  a
  (* FIXME: Something like this should be able to get constructor argument types but I couldn't get it to work *)
  (* let pt = fold_rel_context (fun env (_,_,d) c _ _-> []) (pf_env g)  ~init:([]) rel_context in *)

(* Generate a term of a given type, where there is a limit on how many recursive constructors can be used *)
let rec generate max_depth c =
  dmsgc 3 "Generating term of type " c;
  let constructors = constr_to_constructors c in
  (*  Array.iter dmsg_constructor_summary constructors; *)
  let pick =
    (* Stop picking recursive constructors if depth limit has been reached *)
    if max_depth > 1 then
      constructors.(Random.int (Array.length constructors))
    else
    (
    dmsg 3 (str "Limit reached, picking base case constructor");
      (* Identify non-recursive constructors and pick one *)
      (* A base case constructor of t either has no arguments or arguments that do not refer to t.
         FIXME: Will only identify constructors with no arguments. Need special treatment for e.g. list nat types as
         constructor will say something like list ?1 not list nat *)
      (* let is_recursive = Array.fold_left (fun x t -> x || eq_constr c t) false in *)
      let nr = List.filter (fun x -> (let at = get_constructor_argument_types x in (at = [| |] (*|| is_recursive at = true*))))
        (Array.to_list constructors) in
      if nr = [] then
        (dmsg 0 (str "Could not identify non-recursive constructors! Falling back to picking random constructors but random term generation might not terminate!");
        constructors.(Random.int (Array.length constructors))
        )
      else
        List.nth nr (Random.int (length nr))
    )
    in
  let cat = get_constructor_argument_types pick in
  (* Instantiated constructor (e.g. cons constructor will have list type instantiated ) with mkRel(...) terms where constructor parameters are expected *)
  let inst_constructor = build_dependent_constructor pick in
  dmsgc 3 "inst_constructor" inst_constructor;
  if Array.length cat = 0 then
    inst_constructor
  else
    let generated_constructor_arguments = Array.map (generate (max_depth / 2)) cat in
    (* FIXME: Manually replacing mkRel terms with constructor arguments because I could not
    work out how to construct a lambda term that the arguments list could be applied to *)
    let r = snd(Array.fold_left
      (fun (i,t) r -> (i + 1, replace_term (mkRel i) r t)) (1, inst_constructor)
      generated_constructor_arguments ) in
    dmsgc 3 "replaced" r; r

TACTIC EXTEND generatetest
| [ "generate_term" constr(t) ] -> [ fun g ->
  let value = generate 30 t in
  msgnl (str "generate_term: " ++ (pr_constr value));
  tclIDTAC g]
END

(* FIXME: This needs to be linked to Coq's undo mechanism because undoing "add generator" commands won't undo changes to this map *)
let type_to_generator = Hashtbl.create 1
(* Used for mapping variable replacements e.g. A should be replaced with nat*)
let variable_to_replacement = Hashtbl.create 1

TACTIC EXTEND GenCommand
| [ "Generator" constr(type2) constr(generator)] -> [
  Hashtbl.replace type_to_generator ((*constrOut *)type2) ((*constrOut *)generator);
  tclIDTAC]
END

TACTIC EXTEND ReplaceInTests
| [ "ReplaceInTests" ident(id) constr(replacement_variable)] -> [
  fun g ->
    let rt = (pf_type_of g replacement_variable) in
    constr_display ((mkVar id));
    if is_Set rt then
      (Hashtbl.replace variable_to_replacement (mkVar id) (replacement_variable);tclIDTAC g)
    else
      tclFAIL 0  (str "Can only allow replacements with a variable of type Set") g
  ]
END

exception CounterexampleFound of Pp.std_ppcmds
exception Untestable of Pp.std_ppcmds

(* Fixed RNG seed useful for debugging *)
let use_int_seed = true

(* FIXME: Shouldn't call this at top-level. Is there a way for this module to use its own RNG? *)
if use_int_seed then Random.init 0 else Random.self_init ();;

TACTIC EXTEND Echo23
| [ "quickcheck" constr(depth) integer(examples_to_check) integer(time_limit) integer(log_level)] -> [

  ignore time_limit;

  (* Display counterexample traces and number of examples checked *)
  let explain_counterexample = log_level > 0 in

  (fun g ->

  (* Converts a Coq nat term to a OCaml int term *)
  let rec int_of_coq_nat coq_nat =
      if coq_nat = Lazy.force coq_0 then 0 else
      match kind_of_term coq_nat with
      | App (f, [|next|]) when f = Lazy.force coq_S -> 1 + int_of_coq_nat next
      | _ -> anomaly("Problem converting Coq nat term to OCaml int") in

  let statement_provable p =
    let rec check p =
      dmsgc 3 "statement_provable: " p;
      match kind_of_term p with
        App (f,[|_; lhs; rhs|]) when f = Lazy.force eq_ind ->
          eq_constr (pf_compute g lhs) (pf_compute g rhs)
      | App (f,[|lhs; rhs|])  when f = Lazy.force and_ind ->
          check lhs && check rhs
      | App (f,[|lhs; rhs|])  when f = Lazy.force or_ind ->
          check lhs || check rhs
      | App (f,[|lhs; rhs|])  when f = Lazy.force iff_ind ->
        let iff x y = ((not (x && (not y))) && (not ((not x) && y))) in
          iff (check lhs) (check rhs)
      | Prod (n,t,c) ->
         (match n with
           (* Anonymous Prod used to represent implication *)
           Names.Anonymous -> let imp p q = not(p && (not q)) in imp (check t) (check c)
         | Names.Name i -> (* FIXME: need to check (dependent i c) x to see if this can be treated like a standard implication? *)
           (raise (Untestable (str "Cannot test " ++ pr_constr p))))
      | App (f,[|eq|])  when f = Lazy.force coq_not ->
          not (check eq)
      | App (f,[|lhs; rhs|]) when f = Lazy.force coq_lt ->
        let lhs = pf_compute g lhs in let rhs = pf_compute g rhs in int_of_coq_nat lhs < int_of_coq_nat rhs
      | App (f,[|lhs; rhs|]) when f = Lazy.force coq_le ->
        let lhs = pf_compute g lhs in let rhs = pf_compute g rhs in int_of_coq_nat lhs <= int_of_coq_nat rhs
      | App (f,[|lhs; rhs|]) when f = Lazy.force coq_gt ->
        let lhs = pf_compute g lhs in let rhs = pf_compute g rhs in int_of_coq_nat lhs > int_of_coq_nat rhs
      | App (f,[|lhs; rhs|]) when f = Lazy.force coq_ge ->
        let lhs = pf_compute g lhs in let rhs = pf_compute g rhs in int_of_coq_nat lhs >= int_of_coq_nat rhs
      | _ ->
        (if p = (Lazy.force coq_True) then true
         else if p = (Lazy.force coq_False) then false else
         (raise (Untestable (str "Cannot test term: " ++ pr_constr p))))
    in
    (check p)
  in
  let hyps = pf_hyps g in
  let hyp_id = function (x, _, _) -> x in
  let hyp_type = function (_, _, x) -> x in

  let rec coq_list_to_ocaml_list coq_list =
    let (a1, a2) = destApp coq_list in
    if (Array.length a2 >= 2) then a2.(1)::coq_list_to_ocaml_list a2.(2) else []
  in

  let conclusion = (pf_concl g) in

  (* If a mapping is given by the user, remove assumptions of the form (T:Type) and replace T
    with a user specified type
  *)
  let make_var_replacements (to_replace:(Term.constr * Term.constr) list) (term:constr) =
    List.fold_left
      (fun sofar (variable, replacement)-> replace_term variable replacement sofar)
    term to_replace
  in

  let hashtabl_exists h x = try Hashtbl.find h x;true with Not_found -> false in
  let (vars_to_replace, other_hyps) = List.partition
    (fun (id,_,t) -> is_Type t && hashtabl_exists variable_to_replacement (mkVar id)) hyps in
  let to_replace =
    List.map (fun (id,_,_) ->
      let r =  (try Hashtbl.find variable_to_replacement (mkVar id)
               with Not_found -> (* Shouldn't happen but just replace with itself otherwise *)mkVar id)
      in
      (*if explain_counterexample then msgnl (str "Instantiating " ++ pr_constr (mkVar id) ++ str " with " ++ pr_constr r);*)
      (mkVar(id),r)
    ) vars_to_replace in

  (
  try
    let hyps = List.map (fun (id,x,t) -> (id, x, make_var_replacements to_replace t)) other_hyps in
    let conclusion = make_var_replacements to_replace conclusion in

    (* "Set" variables are testable, others are side-conditions *)
    let (side_conditions, terms_to_replace) =
      List.partition (fun h -> is_Prop (pf_type_of g (hyp_type h))) hyps in

    (* Generate all the values for all types with generators. Should really just do this on demand *)
    let type_to_generated_values = Hashtbl.create 1 in

    Hashtbl.iter
      (fun t gen -> (*msgheading "generaeted";*)
      Hashtbl.add type_to_generated_values t
      (coq_list_to_ocaml_list (pf_reduce cbv_betadeltaiota g (mkApp (gen,[|depth|])))))
      type_to_generator;

    if explain_counterexample then msg (str "Searching for a counterexample ");
    let trivial_examples = ref 0 in

    (* Generate and test examples *)
    for i = 1 to examples_to_check do
      let max_size = 100 in
      let max_size = int_of_float ((((float_of_int i) /. (float_of_int examples_to_check))) *. (float_of_int max_size)) in
        dmsg 3 (str "Generating replacement terms");
        dmsg 3 (str ("Max term replacement size is: " ^ string_of_int max_size));
        let replacements = List.map
          (fun h ->
            (try
              (
              (* Custom term generator (which are just lists of terms of the type we want to generate for now) *)
              let values = Hashtbl.find type_to_generated_values (hyp_type h) in
              let picked = List.nth values (Random.int (List.length values)) in (* lists are slow for this *)
              dmsgc 3 (string_of_id (hyp_id h)) picked;
              (hyp_id h, picked))
            with Not_found ->
              (* Generic random term generator *)
              try
                let generated = generate (max_size) (hyp_type h) in
                ((hyp_id h, generated))
              with _ ->
                raise (Untestable ((str "Generic random term generator failed when generating a term of type ") ++
                  pr_constr (hyp_type h))) )
          )
          terms_to_replace
        in

        let replace_all t =
          List.fold_left (fun r (id, value) -> replace_term (mkVar id) value r) t replacements
        in
        dmsg 3 (str "Testing side-conditions");

        let unsatisfied_side_condition =
          List.exists
            (fun t ->
            let r = replace_all (hyp_type t) in
            dmsg 3 (str (string_of_id (hyp_id t)) ++ (str " := ") ++ (pr_constr r));
            (*dmsgc 1 "after replacement" r;*)
            match statement_provable r with
              true -> (*dmsg 1 (str "sc: satisfied"); *)false
            | false -> (*dmsg 1 (str "sc: not satisfied");*)msg (str "u"); true)
          side_conditions
          in

        let display_example() =
          let b = ref (str "") in
          let msgnl s = b := !b ++ s ++ (str "\n");() in

          msgnl (str " *** COUNTEREXAMPLE FOUND ***\n");
          (* FIXME: pr_... printing commands needs to be coverted to a string before being given to the
             "fail" tactic call because the expected error message does not appear when quickcheck is called
             as Program's "Obligation Tactic" *)
          let fix x = str (string_of_ppcmds x) in

          let rec print_reduction_steps t g =
            msgnl (fix (pr_constr t));
            let simpler = simpl_step (pf_compute g) t in
            if (simpler = t) then () else print_reduction_steps simpler g in

          if replacements <> [] then
            (msgnl (str "Variable instantiations:");
            List.iter (fun (id, value) -> msgnl (str ((string_of_id id) ^ " := ") ++ (fix (pr_constr value))))
              replacements;
            msgnl (str ""));

          if side_conditions <> [] then
            (msgnl (str "All side-conditions were satisfied:");
            List.iter
            (fun t -> let r = replace_all (hyp_type t) in
            msgnl (str (string_of_id (hyp_id t)) ++ (str " : ") ++ (fix (pr_constr r))))
            side_conditions;
            msgnl (str ""));

          msgnl (str "Instantiated and simplified conclusion showing the contradiction:");
          msgnl (fix (pr_constr conclusion));
          let r = replace_all conclusion in
          let step_by_step_simplification = true in
          (if step_by_step_simplification then
            print_reduction_steps r g
          else
            msgnl (fix (pr_constr (pf_reduce cbv_betadeltaiota g conclusion))))
          ;
          msgnl (str "");
          msgnl (str "Original proof obligation:");
          msgnl (fix (pr_goal (sig_it g)));
          flush_all();
          !b
        in

        if unsatisfied_side_condition then
          (trivial_examples := !trivial_examples + 1)
        else
        (
          dmsg 3 (str "Testing conclusion");
          let r = replace_all conclusion in
            (*dmsgc 1 "after replacement" r;*)
            (match statement_provable r with
              true -> if explain_counterexample then msg (str "."); () (*dmsg 1 (str "c: OK")*)
            | false ->
              if explain_counterexample then
              raise (CounterexampleFound (display_example()))
              else
                raise (CounterexampleFound (str "Counterexample found!"))
            ))
    done;

    let nontrivial_percent = 100.0 -. ((((float_of_int !trivial_examples) /. (float_of_int examples_to_check))) *. 100.0) in
    let message =
      sprintf "No counterexample found after %d tests (%.1f%% with satisfied side-conditions)\n" examples_to_check nontrivial_percent in

    if explain_counterexample then tclIDTAC_MESSAGE (str message) g else tclIDTAC g

  with CounterexampleFound s ->
    (* Add a new line to the end of the "Searching..........." search status message *)
    if explain_counterexample then msg (str "");
    tclFAIL 0 s g
  | Not_found -> tclIDTAC_MESSAGE (str "QC: Cannot test goal.") g
  | Untestable m -> tclIDTAC_MESSAGE (str "QC: Untestable conjecture: " ++ m ++ str "\n") g
  | _ ->
    (* Possible cause of failure here is type errors after replacing type variables *)
    tclIDTAC_MESSAGE (str "QC: Unexpected testing failure.") g
  )
  )
]
END
