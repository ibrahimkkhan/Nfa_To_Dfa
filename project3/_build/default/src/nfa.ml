open List
open Sets

(*********)
(* Types *)
(*********)

type ('q, 's) transition = 'q * 's option * 'q

type ('q, 's) nfa_t = {
  sigma: 's list;
  qs: 'q list;
  q0: 'q;
  fs: 'q list;
  delta: ('q, 's) transition list;
}

(***********)
(* Utility *)
(***********)

(* explode converts a string to a character list *)
let explode (s: string) : char list =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l)
  in
  exp (String.length s - 1) []

(****************)
(* Part 1: NFAs *)
(****************)

let move (nfa: ('q,'s) nfa_t) (qs: 'q list) (s: 's option) : 'q list =
   List.fold_left (fun acc delta -> 
    match delta with 
    | (ss, option, fs) -> if option = s && (Sets.elem ss qs )&& (Sets.elem fs acc = false )then fs::acc else acc) [] nfa.delta;;


    
let e_closure (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list =
  let rec find_e_closures compare full_list elem = 
    if compare elem (full_list elem) then elem else find_e_closures compare full_list (full_list elem)
    in find_e_closures (fun qs y -> Sets.eq qs y) (fun qs -> Sets.union (move nfa qs None) qs) qs;;


let accept (nfa: ('q,char) nfa_t) (s: string) : bool =
  let characters = explode s in
    let elem = e_closure nfa [nfa.q0] in
      let states = match characters with
        |[] -> elem
        |_ -> List.fold_left (fun a curr -> e_closure nfa (move nfa a (Some curr))) elem characters 
        in List.fold_left (fun acc curr -> if (List.mem curr nfa.fs = true) then true else acc) false states;;
      
(*******************************)
(* Part 2: Subset Construction *)
(*******************************)


let new_states (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list =
  List.fold_left (fun acc h -> e_closure nfa (move nfa qs (Some h)) :: acc) [] nfa.sigma;;

let new_trans (nfa: ('q,'s) nfa_t) (qs: 'q list) : ('q list, 's) transition list = 
  List.fold_left (fun acc h -> (qs, Some h, (e_closure nfa (move nfa qs (Some h)))) :: acc) [] nfa.sigma;;

let new_finals (nfa: ('q,'s) nfa_t) (qs: 'q list) : 'q list list =
  let rec new_finals_helper lst bools =
    match lst with
    |[] -> if bools = false then false else true
    |h::t -> new_finals_helper t (List.mem h nfa.fs) in
  if (new_finals_helper qs false) then [qs] else [];;

let rec remove_duplicates lst = match lst with
  |[] -> []
  |h::t -> h::(remove_duplicates (List.fold_left (fun a x -> if x<>h then x::a else a) [] t))

let helper_h x nfa dfa work = 
  List.fold_left (fun acc h -> if (h = [] || elem h work || elem h dfa.qs ) then acc else h::acc) [] (new_states nfa x)

  let rec nfa_to_dfa_step (nfa: ('q,'s) nfa_t) (dfa: ('q list, 's) nfa_t)
  (work: 'q list list) : ('q list, 's) nfa_t =
  match work with
    | []-> dfa
    | h::t -> 
    let helper = helper_h h nfa dfa work in
    let full = union helper t in
    let dfa_t = 
    { 
      qs = union [h] dfa.qs;
      sigma =  dfa.sigma;
      delta = union (new_trans nfa h) dfa.delta;
      q0 = dfa.q0;
      fs = remove_duplicates (union (new_finals nfa h) dfa.fs)
    } in nfa_to_dfa_step nfa dfa_t full

    
let nfa_to_dfa (nfa: ('q,'s) nfa_t) : ('q list, 's) nfa_t = 
  let dfa_t =
    {
      qs = [];
      sigma =  nfa.sigma;
      delta = [];
      q0 = e_closure nfa [nfa.q0];
      fs = []
    } in nfa_to_dfa_step nfa dfa_t [dfa_t.q0];;


