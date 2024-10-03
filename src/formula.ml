(*******************************************************************)
(*     This is part of WhyMon, and it is distributed under the     *)
(*     terms of the GNU Lesser General Public License version 3    *)
(*           (see file LICENSE for more details)                   *)
(*                                                                 *)
(*  Copyright 2023:                                                *)
(*  Dmitriy Traytel (UCPH)                                         *)
(*  Leonardo Lima (UCPH)                                           *)
(*******************************************************************)

open Base
open Pred

type t =
  | TT
  | FF
  | EqConst of string * Dom.t
  | Predicate of string * Term.t list
  | Neg of t
  | And of t * t
  | Or of t * t
  | Imp of t * t
  | Iff of t * t
  | Exists of string * t
  | Forall of string * t
  | Prev of Interval.t * t
  | Next of Interval.t * t
  | Once of Interval.t * t
  | Eventually of Interval.t * t
  | Historically of Interval.t * t
  | Always of Interval.t * t
  | Since of Interval.t * t * t
  | Until of Interval.t * t * t
  (* Added mutual constructors *)
  | Frex of Interval.t * regex
  | Prex of Interval.t * regex
(* Added constructors for regex *)
and regex =
  | Wild
  | Test of t
  | Plus of regex * regex
  | Concat of regex * regex
  | Star of regex


let tt = TT
let ff = FF
let eqconst x d = EqConst (x, d)
let predicate p_name trms = Predicate (p_name, check_terms p_name trms)
let neg f = Neg f
let conj f g = And (f, g)
let disj f g = Or (f, g)
let imp f g = Imp (f, g)
let iff f g = Iff (f, g)
let exists x f = Exists (x, f)
let forall x f = Forall (x, f)
let prev i f = Prev (i, f)
let next i f = Next (i, f)
let once i f = Once (i, f)
let eventually i f = Eventually (i, f)
let historically i f = Historically (i, f)
let always i f = Always (i, f)
let since i f g = Since (i, f, g)
let until i f g = Until (i, f, g)

(* Rewriting of non-native operators *)
let trigger i f g = Neg (Since (i, Neg (f), Neg (g)))
let release i f g = Neg (Until (i, Neg (f), Neg (g)))

(* Checks whether x occur in f *)
(* TODO: Merge this function and check_bindings *)
let quant_check x f =
  let rec quant_check_rec = function
  | TT | FF -> false
  | EqConst (y, _) -> String.equal x y
  | Predicate (_, trms) -> List.exists trms ~f:(fun y -> Term.equal (Var x) y)
  | Exists (_, f)
    | Forall (_, f) -> quant_check_rec f
  | Neg f
    | Prev (_, f)
    | Once (_, f)
    | Historically (_, f)
    | Eventually (_, f)
    | Always (_, f)
    | Next (_, f) -> quant_check_rec f
  | And (f1, f2)
    | Or (f1, f2)
    | Imp (f1, f2)
    | Iff (f1, f2)
    | Since (_, f1, f2)
    | Until (_, f1, f2) -> quant_check_rec f1 || quant_check_rec f2
  (* Added cases for regex *)
  (* TODO: Move outside and make mutual... *)
  | Frex (_, r)
    | Prex (_, r) ->
      (* Recursively handle free variables in regular expressions *)
      let rec regex_quant = function
        | Wild -> false                                        (* Wild has no free variables *)
        | Test f -> quant_check_rec f                          (* Use quant_check_rec on the formula in Test *)
        | Plus (r1, r2)  -> regex_quant r1 || regex_quant r2   (* Plus only depends on the free variables in r1 and r2, need to check if x occurs in either r1 or r2 *)
        | Concat (r1, r2) -> regex_quant r1 || regex_quant r2  (* Union of two regexes *)
        | Star r -> regex_quant r                              (* Star only depends on the free variables in r *)
      in
      regex_quant r
  in
  if not (quant_check_rec f) then
    raise (Invalid_argument (Printf.sprintf "bound variable %s does not appear in subformula" x))

let rec equal x y = match x, y with
  | TT, TT | FF, FF -> true
  | EqConst (x, _), EqConst (x', _) -> String.equal x x'
  | Predicate (r, trms), Predicate (r', trms') -> String.equal r r' && List.equal Term.equal trms trms'
  | Neg f, Neg f' -> phys_equal f f'
  | And (f, g), And (f', g')
    | Or (f, g), Or (f', g')
    | Imp (f, g), Imp (f', g')
    | Iff (f, g), Iff (f', g') -> phys_equal f f' && phys_equal g g'
  | Exists (x, f), Exists (x', f')
    | Forall (x, f), Forall (x', f') -> String.equal x x' && phys_equal f f'
  | Prev (i, f), Prev (i', f')
    | Next (i, f), Next (i', f')
    | Once (i, f), Once (i', f')
    | Eventually (i, f), Eventually (i', f')
    | Historically (i, f), Historically (i', f')
    | Always (i, f), Always (i', f') -> Interval.equal i i' && phys_equal f f'
  | Since (i, f, g), Since (i', f', g')
    | Until (i, f, g), Until (i', f', g') -> Interval.equal i i' && phys_equal f f' && phys_equal g g'
  (* Added cases for Frex and Prex - check equality of both the intervals and the regular expressions *)
  | Frex (i, r), Frex (i', r')
    | Prex (i, r), Prex (i', r') -> Interval.equal i i' && regex_equal r r'
  (* TODO: If removed, there's an error... is it due to wrong implementation from my side? *)
  | _ -> false

and regex_equal x y = match x, y with
| Wild, Wild -> true
| Test f, Test f' -> phys_equal f f'
| Plus (r1, r2), Plus (r1', r2')
| Concat (r1, r2), Concat (r1', r2') -> regex_equal r1 r1' && regex_equal r2 r2'
| Star r, Star r' -> regex_equal r r'
| _ -> false 

(* fv: free variable *)  
let rec fv = function
  | TT | FF -> Set.empty (module String)
  | EqConst (x, _) -> Set.of_list (module String) [x]
  | Predicate (_, trms) -> Set.of_list (module String) (Pred.Term.fv_list trms)
  | Exists (x, f)
    | Forall (x, f) -> Set.filter (fv f) ~f:(fun y -> not (String.equal x y))
  | Neg f
    | Prev (_, f)
    | Once (_, f)
    | Historically (_, f)
    | Eventually (_, f)
    | Always (_, f)
    | Next (_, f) -> fv f
  | And (f1, f2)
    | Or (f1, f2)
    | Imp (f1, f2)
    | Iff (f1, f2)
    | Since (_, f1, f2)
    | Until (_, f1, f2) -> Set.union (fv f1) (fv f2)
  (* Added cases for Frex and Prex *)
  | Frex (_, r)
    | Prex (_, r) -> regex_fv r

and regex_fv = function
  | Wild -> Set.empty (module String)
  | Test f -> fv f
  | Plus (r1, r2)
  | Concat (r1, r2) -> Set.union (regex_fv r1) (regex_fv r2) (* recursively compute the union of free variables in their subcomponents *)
  | Star r -> regex_fv r

(* Variable scoping check - verifies bound_vars don't overlap with fv's and that variables are'nt bound more than once within the same scope *)
let check_bindings f =
  let fv_f = fv f in
  let rec check_bindings_rec bound_vars = function
    | TT | FF -> (bound_vars, true)
    | EqConst _ -> (bound_vars, true)
    | Predicate _ -> (bound_vars, true)
    | Exists (x, _)
      | Forall (x, _) -> ((Set.add bound_vars x), (not (Set.mem fv_f x)) && (not (Set.mem bound_vars x)))
    | Neg f
      | Prev (_, f)
      | Once (_, f)
      | Historically (_, f)
      | Eventually (_, f)
      | Always (_, f)
      | Next (_, f) -> check_bindings_rec bound_vars f
    | And (f1, f2)
      | Or (f1, f2)
      | Imp (f1, f2)
      | Iff (f1, f2)
      | Since (_, f1, f2)
      | Until (_, f1, f2) -> let (bound_vars1, b1) = check_bindings_rec bound_vars f1 in
                             let (bound_vars2, b2) = check_bindings_rec (Set.union bound_vars1 bound_vars) f2 in
                             (bound_vars2, b1 && b2) 
    (* Added cases for Frex and Prex *)
    | Frex (_, r)
      | Prex (_, r) -> 
        (* Helper function to check variable bindings for regular expressions *)
        let rec check_bindings_regex bound_vars = function
          | Wild -> (bound_vars, true)                  (* Wild has no variables to bind, thus always valid regarding variable bindings *)
          | Test f -> check_bindings_rec bound_vars f   (* Check variable bindings for the formula f in Test *)
          | Plus (r1, r2) -> let (bound_vars1, b1) = check_bindings_regex bound_vars r1 in
                             let (bound_vars2, b2) = check_bindings_regex (Set.union bound_vars1 bound_vars) r2 in
                             (bound_vars2, b1 && b2)    (* The two regex's are checked independently and are not related except for their bound variables *)
          | Concat (r1, r2) -> let (bound_vars1, b1) = check_bindings_regex bound_vars r1 in
                               let (bound_vars2, b2) = check_bindings_regex (Set.union bound_vars1 bound_vars) r2 in
                               (bound_vars2, b1 && b2)  (* The variables bound in r1 directly affect how r2 is processed *)
          | Star r -> check_bindings_regex bound_vars r (* Repetition of the regex is checked for valid variable bindings *)
      in check_bindings_regex bound_vars r
  in
  snd (check_bindings_rec (Set.empty (module String)) f)

(* Computes columns in table 
Either.first: used for formulas, Either.second: used for regex *)
let rec subfs_dfs h = match h with
  | TT | FF | EqConst _ | Predicate _ -> [Either.first h]
  | Neg f -> [Either.first h] @ (subfs_dfs f)
  | And (f, g) -> [Either.first h] @ (subfs_dfs f) @ (subfs_dfs g)
  | Or (f, g) -> [Either.first h] @ (subfs_dfs f) @ (subfs_dfs g)
  | Imp (f, g) -> [Either.first h] @ (subfs_dfs f) @ (subfs_dfs g)
  | Iff (f, g) -> [Either.first h] @ (subfs_dfs f) @ (subfs_dfs g)
  | Exists (_, f) -> [Either.first h] @ (subfs_dfs f)
  | Forall (_, f) -> [Either.first h] @ (subfs_dfs f)
  | Prev (_, f) -> [Either.first h] @ (subfs_dfs f)
  | Next (_, f) -> [Either.first h] @ (subfs_dfs f)
  | Once (_, f) -> [Either.first h] @ (subfs_dfs f)
  | Eventually (_, f) -> [Either.first h] @ (subfs_dfs f)
  | Historically (_, f) -> [Either.first h] @ (subfs_dfs f)
  | Always (_, f) -> [Either.first h] @ (subfs_dfs f)
  | Since (_, f, g) -> [Either.first h] @ (subfs_dfs f) @ (subfs_dfs g)
  | Until (_, f, g) -> [Either.first h] @ (subfs_dfs f) @ (subfs_dfs g)
  (* Added cases for Frex and Prex *)
  | Frex (_, r)
    | Prex (_, r) -> [Either.first h] @ (subfs_dfs_regex r)

and subfs_dfs_regex = function
  | Wild -> [Either.second Wild]                        (* Wild has no subformulas *)
  | Test f -> [Either.second (Test f)] @ (subfs_dfs f)  (* Test has a subformula f *)
  | Plus (r1, r2) -> [Either.second (Plus (r1, r2))] @ (subfs_dfs_regex r1) @ (subfs_dfs_regex r2) (* Constructs a list with the concatenated regex and appends the results from both sub-expressions *)
  | Concat (r1, r2) -> [Either.second (Concat (r1, r2))] @ (subfs_dfs_regex r1) @ (subfs_dfs_regex r2) (* Constructs a list with the concatenated regex and appends the results from both sub-expressions *)
  | Star r -> [Either.second (Star r)] @ (subfs_dfs_regex r) (* Constructs a list with the star regex and appends the results from the recursively called r *)

(* Computes indices of the columns of the subformulas in the table *)
let subfs_scope h i =
  (* traverses the formula h, computes the indices of subformulas, returning both the updated index and a list representing the subformula scopes *)
  let rec subfs_scope_rec h i =
    match h with
    | TT | FF | EqConst _ | Predicate _ -> (i, [(i, ([], []))])
    | Neg f
      | Exists (_, f)
      | Forall (_, f)
      | Prev (_, f)
      | Next (_, f)
      | Once (_, f)
      | Eventually (_, f)
      | Historically (_, f)
      | Always (_, f) -> let (i', subfs_f) = subfs_scope_rec f (i+1) in
                         (i', [(i, (List.map subfs_f ~f:fst, []))] @ subfs_f)
    | And (f, g)
      | Or (f, g)
      | Imp (f, g)
      | Iff (f, g)
      | Since (_, f, g)
      | Until (_, f, g) ->  let (i', subfs_f) = subfs_scope_rec f (i+1) in
                            let (i'', subfs_g) = subfs_scope_rec g (i'+1) in
                            (i'', [(i, ((List.map subfs_f ~f:fst), (List.map subfs_g ~f:fst)))]
                                  @ subfs_f @ subfs_g) 
    (* Added cases for regexes *)
    | Frex (_, r)
      | Prex (_, r) -> 
        let rec regex_scope r i =
          match r with
            | Wild -> (i, [(i, ([], []))])
            | Test f -> let (i', subfs_f) = subfs_scope_rec f (i+1) in  
                        (i', [(i, (List.map subfs_f ~f:fst, []))] @ subfs_f) (* evaluates whether f holds *)
            | Plus (r1, r2) -> let (i', subfs_r1) = regex_scope r1 i in
                               let (i'', subfs_r2) = regex_scope r2 (i'+1) in
                               (i'', [(i, (List.map subfs_r1 ~f:fst, List.map subfs_r2 ~f:fst))] 
                                     @ subfs_r1 @ subfs_r2)
            | Concat (r1, r2) -> let (i', subfs_r1) = regex_scope r1 i in 
                                 let (i'', subfs_r2) = regex_scope r2 (i'+1) in 
                                  (i'', [(i, (List.map subfs_r1 ~f:fst, List.map subfs_r2 ~f:fst))] 
                                        @ subfs_r1 @ subfs_r2)
            | Star r -> let (i', subfs_r) = regex_scope r i in
                        (i', [(i, (List.map subfs_r ~f:fst, []))] @ subfs_r)
        in regex_scope r i
    in
  snd (subfs_scope_rec h i)

let rec preds = function
  | TT | FF | EqConst _ -> []
  | Predicate (r, trms) -> [Predicate (r, trms)]
  | Neg f | Exists (_, f) | Forall (_, f)
    | Next (_, f) | Prev (_, f)
    | Once (_, f) | Historically (_, f)
    | Eventually (_, f) | Always (_, f) -> preds f
  | And (f1, f2) | Or (f1, f2)
    | Imp (f1, f2) | Iff (f1, f2)
    | Until (_, f1, f2) | Since (_, f1, f2) -> let a1s = List.fold_left (preds f1) ~init:[]
                                                           ~f:(fun acc a -> if List.mem acc a ~equal:equal then acc
                                                                            else acc @ [a])  in
                                               let a2s = List.fold_left (preds f2) ~init:[]
                                                           ~f:(fun acc a ->
                                                             if (List.mem acc a ~equal:equal) || (List.mem a1s a ~equal:equal) then acc
                                                             else acc @ [a]) in
                                               List.append a1s a2s
    (* Added cases for Frex and Prex *)
  | Frex (_, r)
    | Prex (_, r) -> regex_preds r

and regex_preds = function
  | Wild -> []
  | Test f -> preds f
  | Plus (r1, r2) -> List.append (regex_preds r1) (regex_preds r2)
  | Concat (r1, r2) -> List.append (regex_preds r1) (regex_preds r2)
  | Star r -> regex_preds r

(* Returns the set of predicate names in a formula and a regex *)
let pred_names f =
  let rec pred_names_rec s = function
    | TT | FF | EqConst _ -> s
    | Predicate (r, _) -> Set.add s r
    | Neg f | Exists (_, f) | Forall (_, f)
      | Prev (_, f) | Next (_, f)
      | Once (_, f) | Eventually (_, f)
      | Historically (_, f) | Always (_, f) -> pred_names_rec s f
    | And (f1, f2) | Or (f1, f2)
      | Imp (f1, f2) | Iff (f1, f2)
      | Until (_, f1, f2) | Since (_, f1, f2) -> Set.union (pred_names_rec s f1) (pred_names_rec s f2) 
      (* Added cases for Frex and Prex *)
      | Frex (_, r) 
        | Prex (_, r) -> regex_pred_names s r
    and regex_pred_names s = function
      | Wild -> s
      | Test f -> pred_names_rec s f
      | Plus (r1, r2) -> Set.union (regex_pred_names s r1) (regex_pred_names s r2)
      | Concat (r1, r2) -> Set.union (regex_pred_names s r1) (regex_pred_names s r2)
      | Star r -> regex_pred_names s r
    in
  pred_names_rec (Set.empty (module String)) f

(* Converts each logical formula/regular expression type into it's string form *)
let rec op_to_string = function
  | TT -> Printf.sprintf "⊤"
  | FF -> Printf.sprintf "⊥"
  | EqConst _ -> Printf.sprintf "="
  | Predicate (r, trms) -> Printf.sprintf "%s(%s)" r (Term.list_to_json_string trms)
  | Neg _ -> Printf.sprintf "¬"
  | And (_, _) -> Printf.sprintf "∧"
  | Or (_, _) -> Printf.sprintf "∨"
  | Imp (_, _) -> Printf.sprintf "→"
  | Iff (_, _) -> Printf.sprintf "↔"
  | Exists (x, _) -> Printf.sprintf "∃ %s." x
  | Forall (x, _) -> Printf.sprintf "∀ %s." x
  | Prev (i, _) -> Printf.sprintf "●%s" (Interval.to_string i)
  | Next (i, _) -> Printf.sprintf "○%s" (Interval.to_string i)
  | Once (i, _) -> Printf.sprintf "⧫%s" (Interval.to_string i)
  | Eventually (i, _) -> Printf.sprintf "◊%s" (Interval.to_string i)
  | Historically (i, _) -> Printf.sprintf "■%s" (Interval.to_string i)
  | Always (i, _) -> Printf.sprintf "□%s" (Interval.to_string i)
  | Since (i, _, _) -> Printf.sprintf "S%s" (Interval.to_string i)
  | Until (i, _, _) -> Printf.sprintf "U%s" (Interval.to_string i)
  | Frex (i, _) -> Printf.sprintf "F%s" (Interval.to_string i)
  | Prex (i, _) -> Printf.sprintf "P%s" (Interval.to_string i)

(* TODO: Is this what is how I was supposed to think about the function? *)
and op_to_string_regex = function
  | Wild -> Printf.sprintf "Wild"
  | Test f -> Printf.sprintf "(%s)" (op_to_string f) (* Handles regexes that test for formula, f, printing it in the form (f), where f is represented by op_to_string *)
  | Plus (r1, r2) -> Printf.sprintf "(%s ∪ %s)" (op_to_string_regex r1) (op_to_string_regex r2)
  | Concat (r1, r2) -> Printf.sprintf "(%s ∙ %s)" (op_to_string_regex r1) (op_to_string_regex r2)
  | Star r -> Printf.sprintf "(%s)*" (op_to_string_regex r)

let rec to_string_rec l json = function
  | TT -> Printf.sprintf "⊤"
  | FF -> Printf.sprintf "⊥"
  | EqConst (x, c) -> Printf.sprintf "%s = %s" x (Dom.to_string c)
  | Predicate (r, trms) -> if json then Printf.sprintf "%s(%s)" r (Term.list_to_json_string trms)
                           else Printf.sprintf "%s(%s)" r (Term.list_to_string trms)
  | Neg f -> Printf.sprintf "¬%a" (fun _ -> to_string_rec 5 json) f
  | And (f, g) -> Printf.sprintf (Etc.paren l 4 "%a ∧ %a") (fun _ -> to_string_rec 4 json) f (fun _ -> to_string_rec 4 json) g
  | Or (f, g) -> Printf.sprintf (Etc.paren l 3 "%a ∨ %a") (fun _ -> to_string_rec 3 json) f (fun _ -> to_string_rec 4 json) g
  | Imp (f, g) -> Printf.sprintf (Etc.paren l 5 "%a → %a") (fun _ -> to_string_rec 5 json) f (fun _ -> to_string_rec 5 json) g
  | Iff (f, g) -> Printf.sprintf (Etc.paren l 5 "%a ↔ %a") (fun _ -> to_string_rec 5 json) f (fun _ -> to_string_rec 5 json) g
  | Exists (x, f) -> Printf.sprintf (Etc.paren l 5 "∃%s. %a") x (fun _ -> to_string_rec 5 json) f
  | Forall (x, f) -> Printf.sprintf (Etc.paren l 5 "∀%s. %a") x (fun _ -> to_string_rec 5 json) f
  | Prev (i, f) -> Printf.sprintf (Etc.paren l 5 "●%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5 json) f
  | Next (i, f) -> Printf.sprintf (Etc.paren l 5 "○%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5 json) f
  | Once (i, f) -> Printf.sprintf (Etc.paren l 5 "⧫%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5 json) f
  | Eventually (i, f) -> Printf.sprintf (Etc.paren l 5 "◊%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5 json) f
  | Historically (i, f) -> Printf.sprintf (Etc.paren l 5 "■%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5 json) f
  | Always (i, f) -> Printf.sprintf (Etc.paren l 5 "□%a %a") (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5 json) f
  | Since (i, f, g) -> Printf.sprintf (Etc.paren l 0 "%a S%a %a") (fun _ -> to_string_rec 5 json) f
                         (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5 json) g
  | Until (i, f, g) -> Printf.sprintf (Etc.paren l 0 "%a U%a %a") (fun _ -> to_string_rec 5 json) f
                         (fun _ -> Interval.to_string) i (fun _ -> to_string_rec 5 json) g
  | _ -> failwith "not implemented"
let to_string json = to_string_rec 0 json

let rec to_json_rec indent pos f =
  let indent' = "  " ^ indent in
  match f with
  | TT -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"TT\"\n%s}"
            indent pos indent' indent
  | FF -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"FF\"\n%s}"
            indent pos indent' indent
  | EqConst (x, c) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"EqConst\",\n%s\"variable\": \"%s\",\n%s\"constant\": \"%s\"\n%s}"
                         indent pos indent' indent' x indent' (Dom.to_string c) indent
  | Predicate (r, trms) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Predicate\",\n%s\"name\": \"%s\",\n%s\"terms\": \"%s\"\n%s}"
                             indent pos indent' indent' r indent' (Term.list_to_string trms) indent
  | Neg f -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Neg\",\n%s\n%s}"
               indent pos indent' (to_json_rec indent' "" f) indent
  | And (f, g) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"And\",\n%s,\n%s\n%s}"
                    indent pos indent' (to_json_rec indent' "l" f) (to_json_rec indent' "r" g) indent
  | Or (f, g) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Or\",\n%s,\n%s\n%s}"
                   indent pos indent' (to_json_rec indent' "l" f) (to_json_rec indent' "r" g) indent
  | Imp (f, g) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Imp\",\n%s,\n%s\n%s}"
                    indent pos indent' (to_json_rec indent' "l" f) (to_json_rec indent' "r" g) indent
  | Iff (f, g) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Iff\",\n%s,\n%s\n%s}"
                    indent pos indent' (to_json_rec indent' "l" f) (to_json_rec indent' "r" g) indent
  | Exists (x, _) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Exists\",\n%s\"variable\": \"%s\",\n%s\n%s}"
                       indent pos indent' indent' x (to_json_rec indent' "" f) indent
  | Forall (x, _) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Forall\",\n%s\"variable\": \"%s\",\n%s\n%s}"
                       indent pos indent' indent' x (to_json_rec indent' "" f) indent
  | Prev (i, f) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Prev\",\n%s\"Interval.t\": \"%s\",\n%s\n%s}"
                     indent pos indent' indent' (Interval.to_string i) (to_json_rec indent' "" f) indent
  | Next (i, f) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Next\",\n%s\"Interval.t\": \"%s\",\n%s\n%s}"
                     indent pos indent' indent' (Interval.to_string i) (to_json_rec indent' "" f) indent
  | Once (i, f) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Once\",\n%s\"Interval.t\": \"%s\",\n%s\n%s}"
                     indent pos indent' indent' (Interval.to_string i) (to_json_rec indent' "" f) indent
  | Eventually (i, f) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Eventually\",\n%s\"Interval.t\": \"%s\",\n%s\n%s}"
                           indent pos indent' indent' (Interval.to_string i) (to_json_rec indent' "" f) indent
  | Historically (i, f) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Historically\",\n%s\"Interval.t\": \"%s\",\n%s\n%s}"
                             indent pos indent' indent' (Interval.to_string i) (to_json_rec indent' "" f) indent
  | Always (i, f) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Always\",\n%s\"Interval.t\": \"%s\",\n%s\n%s}"
                       indent pos indent' indent' (Interval.to_string i) (to_json_rec indent' "" f) indent
  | Since (i, f, g) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Since\",\n%s\"Interval.t\": \"%s\",\n%s,\n%s\n%s}"
                         indent pos indent' indent' (Interval.to_string i) (to_json_rec indent' "l" f) (to_json_rec indent' "r" g) indent
  | Until (i, f, g) -> Printf.sprintf "%s\"%sformula\": {\n%s\"type\": \"Until\",\n%s\"Interval.t\": \"%s\",\n%s,\n%s\n%s}"
                         indent pos indent' indent' (Interval.to_string i) (to_json_rec indent' "l" f) (to_json_rec indent' "r" g) indent
  | _ -> failwith "not implemented"
let to_json = to_json_rec "    " ""

let rec to_latex_rec l = function
  | TT -> Printf.sprintf "\\top"
  | FF -> Printf.sprintf "\\bot"
  | EqConst (x, c) -> Printf.sprintf "%s = %s" (Etc.escape_underscores x) (Dom.to_string c)
  | Predicate (r, trms) -> Printf.sprintf "%s\\,(%s)" (Etc.escape_underscores r) (Term.list_to_string trms)
  | Neg f -> Printf.sprintf "\\neg %a" (fun _ -> to_latex_rec 5) f
  | And (f, g) -> Printf.sprintf (Etc.paren l 4 "%a \\land %a") (fun _ -> to_latex_rec 4) f (fun _ -> to_latex_rec 4) g
  | Or (f, g) -> Printf.sprintf (Etc.paren l 3 "%a \\lor %a") (fun _ -> to_latex_rec 3) f (fun _ -> to_latex_rec 4) g
  | Imp (f, g) -> Printf.sprintf (Etc.paren l 5 "%a \\rightarrow %a") (fun _ -> to_latex_rec 5) f (fun _ -> to_latex_rec 5) g
  | Iff (f, g) -> Printf.sprintf (Etc.paren l 5 "%a \\leftrightarrow %a") (fun _ -> to_latex_rec 5) f (fun _ -> to_latex_rec 5) g
  | Exists (x, f) -> Printf.sprintf (Etc.paren l 5 "\\exists %s. %a") x (fun _ -> to_latex_rec 5) f
  | Forall (x, f) -> Printf.sprintf (Etc.paren l 5 "\\forall %s. %a") x (fun _ -> to_latex_rec 5) f
  | Prev (i, f) -> Printf.sprintf (Etc.paren l 5 "\\Prev{%a} %a") (fun _ -> Interval.to_latex) i (fun _ -> to_latex_rec 5) f
  | Next (i, f) -> Printf.sprintf (Etc.paren l 5 "\\Next{%a} %a") (fun _ -> Interval.to_latex) i (fun _ -> to_latex_rec 5) f
  | Once (i, f) -> Printf.sprintf (Etc.paren l 5 "\\Once{%a} %a") (fun _ -> Interval.to_latex) i (fun _ -> to_latex_rec 5) f
  | Eventually (i, f) -> Printf.sprintf (Etc.paren l 5 "\\Eventually{%a} %a") (fun _ -> Interval.to_latex) i (fun _ -> to_latex_rec 5) f
  | Historically (i, f) -> Printf.sprintf (Etc.paren l 5 "\\Historically{%a} %a") (fun _ -> Interval.to_latex) i (fun _ -> to_latex_rec 5) f
  | Always (i, f) -> Printf.sprintf (Etc.paren l 5 "\\Always{%a} %a") (fun _ -> Interval.to_latex) i (fun _ -> to_latex_rec 5) f
  | Since (i, f, g) -> Printf.sprintf (Etc.paren l 0 "%a \\Since{%a} %a") (fun _ -> to_latex_rec 5) f
                         (fun _ -> Interval.to_latex) i (fun _ -> to_latex_rec 5) g
  | Until (i, f, g) -> Printf.sprintf (Etc.paren l 0 "%a \\Until{%a} %a") (fun _ -> to_latex_rec 5) f
                         (fun _ -> Interval.to_latex) i (fun _ -> to_latex_rec 5) g
  | _ -> failwith "not implemented"
let to_latex = to_latex_rec 0
